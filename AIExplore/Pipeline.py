import json
import re
import subprocess
import textwrap
from pathlib import Path

# All paths are based on this script, not on the terminal's current directory.
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent                         # Folder containing lakefile.toml
INPUT = HERE / "Test.lean"
TEMP = HERE / "_PipelineCandidate.lean"
CLAUDE = Path.home() / ".local" / "bin" / "claude.exe"
MAX_ATTEMPTS = 6

# MVP input format: exactly one line containing only "sorry" (with indentation).
SORRY_LINE = re.compile(r"(?m)^(?P<indent>[ \t]*)sorry[ \t]*$")
IMPORT_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|unsafe|run_tac|native_decide|set_option|import)\b|#(?:exit|eval|print)")


def get_input():
    source = INPUT.read_text(encoding="utf-8")
    if len(SORRY_LINE.findall(source)) != 1:
        raise ValueError("Test.lean must have exactly one standalone 'sorry' line.")
    # This first version deliberately expects no user-written imports.
    if re.search(r"(?m)^\s*import\s+", source):
        raise ValueError("For this version, remove imports from Test.lean first.")
    return source


def ask_claude(source, imports, previous_code="", feedback=""):
    prompt = f"""You are solving a Lean 4 + Mathlib theorem in an existing Lake project.
Return ONLY a valid JSON object with exactly these fields:
{{"imports": ["Mathlib.Data.Nat.Basic"], "proof": "omega"}}
- imports: array of module names WITHOUT the keyword 'import'.
- proof: ONLY the Lean tactic lines replacing the single standalone 'sorry' line.
  Do NOT include 'by' if the input already uses ':= by'.
- Do not modify the theorem statement or any other existing source.
- Do not use 'import Mathlib' (the umbrella import); use specific modules.
- Never use sorry, admit, new axioms, unsafe or proof-bypassing tactics.
- On repair, keep all previous imports. You may add more.
- Do not use Markdown code fences or provide explanations.

ORIGINAL LEAN INPUT (read-only):
{source}

CURRENT IMPORTS (must preserve):
{json.dumps(imports, ensure_ascii=False)}

PREVIOUS GENERATED FILE:
{previous_code or '(first attempt)'}

RAW LEAN ERROR / FEEDBACK:
{feedback[:6000] if feedback else '(none yet)'}
"""
    result = subprocess.run(
        [str(CLAUDE), "-p", "--tools", ""],
        input=prompt, cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
        errors="replace", timeout=240,
    )
    if result.returncode != 0:
        raise RuntimeError("Claude CLI failed:\n" + (result.stderr or result.stdout)[:3000])
    return result.stdout.strip()


def parse_answer(answer):
    # Accommodate occasional ```json fences despite our prompt.
    answer = answer.strip()
    if answer.startswith("```"):
        answer = re.sub(r"^```(?:json)?\s*|\s*```$", "", answer).strip()
    data = json.loads(answer)
    if not isinstance(data, dict):
        raise ValueError("Claude did not return a JSON object")
    imports, proof = data["imports"], data["proof"]
    if not isinstance(imports, list) or not isinstance(proof, str):
        raise ValueError("Invalid imports/proof types")
    for name in imports:
        if not isinstance(name, str) or not IMPORT_NAME.fullmatch(name):
            raise ValueError(f"Invalid import module: {name!r}")
        if name == "Mathlib":
            raise ValueError("Broad 'import Mathlib' is not allowed")
    proof = textwrap.dedent(proof).strip("\n")
    if not proof.strip() or FORBIDDEN.search(proof):
        raise ValueError("Empty or disallowed proof tactic")
    return imports, proof


def assemble(source, imports, proof):
    match = SORRY_LINE.search(source)
    indent = match.group("indent")
    # Each additional tactic line gets the original indentation of sorry.
    lines = proof.splitlines()
    replacement = ("\n" + indent).join(lines)
    body = source[:match.start()] + indent + replacement + source[match.end():]
    header = "".join(f"import {mod}\n" for mod in imports)
    return header + ("\n" if header else "") + body


def check_lean(code):
    TEMP.write_text(code, encoding="utf-8")
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(TEMP)], cwd=ROOT,
            capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=120,
        )
    except subprocess.TimeoutExpired:
        return False, "Lean checking timed out after 120 seconds."
    except OSError as exc:
        return False, f"Could not start Lean: {exc}"
    message = (result.stdout + "\n" + result.stderr).strip()
    # Lean can accept files with sorry and only issue a warning.
    invalid = re.search(r"\b(sorryAx|declaration uses ['\"]sorry['\"]|admitted)\b", message)
    return result.returncode == 0 and not invalid, message


def prune_imports(source, imports, proof):
    remaining = list(imports)
    for name in list(imports):
        trial = remaining.copy()
        trial.remove(name)
        ok, _ = check_lean(assemble(source, trial, proof))
        if ok:
            remaining = trial
            print(f"  Removed unused import: {name}")
        else:
            print(f"  Kept import: {name}")
    return remaining


def main():
    if not (ROOT / "lakefile.toml").exists():
        raise FileNotFoundError(f"Lake project not found: {ROOT}")
    if not CLAUDE.is_file():
        raise FileNotFoundError(f"Claude executable not found: {CLAUDE}")
    source = get_input()
    imports = []
    code = ""
    feedback = ""
    final_proof = None
    try:
        for attempt in range(1, MAX_ATTEMPTS + 1):
            print(f"\n=== Claude attempt {attempt}/{MAX_ATTEMPTS} ===")
            try:
                reply = ask_claude(source, imports, code, feedback)
                new_imports, proof = parse_answer(reply)
                # Imports never disappear during the repair loop.
                imports = list(dict.fromkeys(imports + new_imports))
                code = assemble(source, imports, proof)
                ok, feedback = check_lean(code)
            except RuntimeError as exc:
                # A CLI invocation failure is not a Lean error: do not retry it as a proof repair.
                print(f"Claude invocation failed: {exc}")
                break
            except (ValueError, KeyError, TypeError) as exc:
                feedback = f"Invalid model response: {exc}"
                print(feedback)
                continue
            print("Lean accepted the candidate." if ok else f"Lean rejected:\n{feedback[:3000]}")
            if ok:
                final_proof = proof
                break

        if final_proof is None:
            print("\nNo verified proof. Original Test.lean was NOT modified.")
            return

        print("\n=== Import pruning ===")
        imports = prune_imports(source, imports, final_proof)
        final_code = assemble(source, imports, final_proof)
        ok, message = check_lean(final_code)
        if not ok:
            raise RuntimeError("Final check failed; Test.lean unchanged:\n" + message)
        INPUT.write_text(final_code, encoding="utf-8")
        print(f"\nSUCCESS: verified proof saved to {INPUT}")
        print("Final imports:", imports)
    finally:
        TEMP.unlink(missing_ok=True)


if __name__ == "__main__":
    main()

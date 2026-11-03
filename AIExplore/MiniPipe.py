# 导入Python自带的subprocess模块，让程序能够启动外部命令，例如lake env lean。
import subprocess

# The Lean code before the proof: the imports and the theorem statement.
HEADER = """import Mathlib.Tactic.Ring

theorem ai_sq_expand (x y : Int) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
"""

# The tactics to try, in this order.
TACTICS = ["simp", "omega", "ring"]


def check_with_lean(tactic):
    """Send the theorem plus one tactic to Lean. Return True if Lean accepts it."""
    lean_code = HEADER + "  " + tactic + "\n"
    result = subprocess.run(
        ["lake", "env", "lean", "--stdin"],  # the command to run
        input=lean_code,                     # the text Lean reads as its file
        capture_output=True,                 # collect Lean's messages
        text=True,
        encoding="utf-8",
    )
    if result.returncode == 0:
        return True
    print(result.stdout + result.stderr)
    return False


def main():
    for tactic in TACTICS:
        print("Trying:", tactic)
        if check_with_lean(tactic):
            print("Success! Lean accepts the proof:", tactic)
            return
        print("Failed.")
    print("None of the tactics worked.")


main()

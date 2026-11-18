import Init.Data.Function
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Valuation.Discrete.Basic

inductive PSZ where
  | zero : PSZ
  | p : Nat.Primes → PSZ

def PSZ.toNat (n : PSZ) : Nat :=
  match n with
  | .zero => 0
  | .p n => n.val

instance : TopologicalSpace PSZ where
  IsOpen := fun S => S = ⊤ ∨ S = ⊥ ∨ (∃ T : Set Nat.Primes, T.Finite ∧ Sᶜ = PSZ.p '' T)
  isOpen_univ := by simp only [Set.top_eq_univ, true_or]
  isOpen_inter := by
    rintro S₁ S₂ (rfl | rfl | ⟨T₁, hT₁, h₁⟩) (rfl | rfl | ⟨T₂, hT₂, h₂⟩)
    · left; simp only [le_refl, inf_of_le_left]
    · right; left; simp only [Set.top_eq_univ, Set.subset_univ, inf_of_le_right]
    · right; right
      refine ⟨T₂, hT₂, ?_⟩
      simpa only [Set.top_eq_univ, Set.subset_univ, inf_of_le_right] using h₂
    · right; left; simp only [Set.top_eq_univ, Set.subset_univ, inf_of_le_left]
    · right; left; simp only [le_refl, inf_of_le_left]
    · right; left; simp only [Set.bot_eq_empty, Set.empty_subset, inf_of_le_left]
    · right; right
      refine ⟨T₁, hT₁, ?_⟩
      simpa only [Set.top_eq_univ, Set.subset_univ, inf_of_le_left] using h₁
    · right; left; simp only [Set.bot_eq_empty, Set.empty_subset, inf_of_le_right]
    · right; right
      refine ⟨T₁ ∪ T₂, hT₁.union hT₂, ?_⟩
      rw [Set.compl_inter, h₁, h₂, Set.image_union]
  isOpen_sUnion := fun F hF => by
    by_cases htop : ⊤ ∈ F
    · left
      exact top_unique (Set.subset_sUnion_of_mem htop)
    by_cases hex : ∃ S ∈ F, ∃ T : Set Nat.Primes, T.Finite ∧ Sᶜ = PSZ.p '' T
    · obtain ⟨S₀, hS₀, T₀, hT₀, h₀⟩ := hex
      right; right
      refine ⟨{ t ∈ T₀ | PSZ.p t ∈ (⋃₀ F)ᶜ }, hT₀.subset fun t ht => ht.1, ?_⟩
      ext x
      constructor
      · intro hx
        have hx0 : x ∈ S₀ᶜ := fun h => hx (Set.mem_sUnion_of_mem h hS₀)
        rw [h₀] at hx0
        obtain ⟨t, ht, rfl⟩ := hx0
        exact ⟨t, ⟨ht, hx⟩, rfl⟩
      · rintro ⟨t, ⟨_, hmem⟩, rfl⟩
        exact hmem
    · right; left
      rw [Set.bot_eq_empty, Set.sUnion_eq_empty]
      intro S hS
      rcases hF S hS with h | h | h
      · exact absurd (h ▸ hS) htop
      · exact h
      · exact absurd ⟨S, hS, h⟩ hex

def PSZ1 := Option Nat.Primes

instance : TopologicalSpace PSZ1 where
  IsOpen := fun S => S = ⊤ ∨ S = ⊥ ∨ (∃ T : Set Nat.Primes, T.Finite ∧ Sᶜ = Option.some '' T)
  isOpen_univ := by simp only [Set.top_eq_univ, true_or]
  isOpen_inter := sorry
  isOpen_sUnion := sorry

inductive GridPoint where
  | mk : ℕ → ℕ → GridPoint

def GridPoint.add (a b : GridPoint) : GridPoint := mk (a.1 + b.1) (a.2 + b.2)

instance : Add GridPoint where
  add := GridPoint.add

def GridPoint.zero : GridPoint := mk 0 0

instance : Zero GridPoint where
  zero := GridPoint.zero

lemma GridPoint.add_zero (a : GridPoint) : a + 0 = a := rfl

lemma GridPoint.zero_add (a : GridPoint) : 0 + a = a := by
  change mk (0 + a.1) (0 + a.2) = a
  simp only [Nat.zero_add]

def ParityRel (m n  : ℤ) : Prop := (m % 2) = (n % 2)

def ParityClass : Type 1 :=
  { T : Type // ∃ n : ℤ, T = { m : ℤ // ParityRel m n } }

def ParityClass.zero : ParityClass where
  val := { m : ℤ // ParityRel m 0 }
  property := ⟨0, rfl⟩

def ParityClass.one : ParityClass where
  val := { m : ℤ // ParityRel m 1 }
  property := ⟨1, rfl⟩

theorem ParityClass.five_eq_one :
    ⟨{ m : ℤ // ParityRel m 5 }, 894383957349573948734987345987989, rfl⟩ = ParityClass.one := rfl

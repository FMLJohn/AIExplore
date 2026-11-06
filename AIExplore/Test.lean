import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

theorem q3_deriv_sin_square_plus_cos_square (x : ℝ) :
    deriv (fun y : ℝ => Real.sin y ^ 2 + Real.cos y ^ 2) x = 0 := by
  simp only [Real.sin_sq_add_cos_sq, deriv_const]

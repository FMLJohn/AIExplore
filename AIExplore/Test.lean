import Mathlib.Analysis.SpecificLimits.Basic

theorem q1_reciprocal_tends_to_zero :
    Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop (nhds 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

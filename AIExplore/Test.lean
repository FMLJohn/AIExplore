import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic

theorem q10_trace_conj_invariant (A P Q : Matrix (Fin 2) (Fin 2) ℝ) (h : Q * P = 1) :
    Matrix.trace (P * A * Q) = Matrix.trace A := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]

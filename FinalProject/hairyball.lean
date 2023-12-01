import Mathlib

open RealInnerProductSpace

-- def E n := EuclideanSpace ℝ (Fin n)

structure IsSphVF {n : ℕ} (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) where
  diff : ContDiff ℝ ⊤ v
  perp : ∀x, ‖x‖ = 1 → ⟪x, v x⟫ = 0

structure IsEqvSphVF {n : ℕ}
  (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) extends IsSphVF v where
  equiv : ∀ r > (0 : ℝ), ∀ x, v (r * x) = r * v x

theorem hairy_ball {n} {v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (h : IsSphVF v) (h' : ∀x, ‖x‖ = 1 → v x ≠ 0) : Even n :=
  sorry



open MeasureTheory Metric ENNReal

#check volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)

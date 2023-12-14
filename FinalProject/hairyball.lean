import Mathlib

open RealInnerProductSpace

notation "E" n:30 => EuclideanSpace ℝ (Fin n)

structure IsSphVF {n : ℕ} (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) where
  diff : ContDiff ℝ ⊤ v
  perp : ∀x, ‖x‖ = 1 → ⟪x, v x⟫ = 0

structure IsEqvSphVF {n : ℕ}
  (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) extends IsSphVF v where
  equiv : ∀ r > (0 : ℝ), ∀ x, v (r • x) = r • v x

open Polynomial MeasureTheory Metric ENNReal Topology

def IsPolynomialFun (f : ℝ → ℝ) := ∃ P : ℝ[X], f = P.eval

example (P Q : ℝ[X]) (h : P.eval = Q.eval) : P = Q := Polynomial.funext (congrFun h)

lemma c1_implies_lipschitz (v : E n → E n) (hv : ContDiff ℝ ⊤ v) (A : Set (E n)) (hA : Convex ℝ A) : ∃ K : NNReal, LipschitzWith K (Set.restrict A v) := by

  sorry

lemma sqrt_poly {n} (h : IsPolynomialFun (fun x ↦ (1 + x^2)^(n / 2))) : Even n := by
  let q : ℝ → ℝ := fun x ↦ (1 + x^2)^(n / 2 : ℝ)
  have hq : IsPolynomialFun (q * q) := by
    use (1 + X^2)^n
    ext z
    simp
    rw [← Real.rpow_add, ← Real.rpow_nat_cast]
    field_simp
    positivity
  rcases hq with ⟨k, hk⟩

  have h : ∀ (x : ℝ) (p * p - q * q).eval x = 0 := sorry
  have bruh := zero_of_eval_zero p*p-q*q
  sorry

lemma poly_transform (v : E n → E n) (hv : ContDiff ℝ ⊤ v) (A : Set (E n)) (hA : IsCompact A) :
  ∀ᶠ t in 𝓝 0, (Function.Injective (fun x : A ↦ x + t • (v x)) ∧
  IsPolynomialFun (fun t ↦ volume ((fun x : A ↦ x + t • (v x))''A))) := sorry

theorem hairy_ball_aux {n} {v : E n → E n} (h : IsEqvSphVF v) (h' : ∀x, ‖x‖ = 1 → v x ≠ 0) : Even n := sorry

theorem hairy_ball {n} {v : E n → E n} (h : IsSphVF v) (h' : ∀x, ‖x‖ = 1 → v x ≠ 0) : Even n := sorry



#check volume (ball (0 : E 3) 1)

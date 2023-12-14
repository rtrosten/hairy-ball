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

def suff_small_inj (f: ℝ → E n → E n) := ∀ᶠ t in 𝓝 (0:ℝ), Function.Injective (f t)
def suff_small_surj (f: ℝ → E n → E n) := ∀ᶠ t in 𝓝 (0:ℝ), Function.Surjective (f t)
def IsPolynomialFun (f : ℝ → ℝ) := ∃ P : ℝ[X], f = P.eval

example (P Q : ℝ[X]) (h : P.eval = Q.eval) : P = Q := Polynomial.funext (congrFun h)


lemma smooth_imp_c1 (v : E n → E n) (hv : ContDiff ℝ ⊤ v) : ContDiff ℝ 1 v :=
  hv.of_le le_top

lemma c1_implies_lipschitz (v : E n → E n) (hv : ContDiff ℝ ⊤ v) : ∃ K, LipschitzWith K v := by sorry
lemma sqrt_poly {n} (h : IsPolynomialFun (fun x ↦ (1+x^2)^(n/2))) : Even n := by

  let q : ℝ → ℝ := fun x ↦ (1 + x^2)^(n/2 : ℝ)
  have hq : IsPolynomialFun (q*q) := by
    use (1+X^2)^n
    ext z
    simp
    rw [← Real.rpow_add, ← Real.rpow_nat_cast]
    field_simp
    positivity
  rcases hq with ⟨k, hk⟩
  sorry


theorem hairy_ball_aux {n} {v : E n → E n} (h : IsEqvSphVF v) (h' : ∀x, ‖x‖ = 1 → v x ≠ 0) : Even n := sorry

theorem hairy_ball {n} {v : E n → E n} (h : IsSphVF v) (h' : ∀x, ‖x‖ = 1 → v x ≠ 0) : Even n := by
  let f : ℝ → E n → E n := fun t ↦ (fun x ↦ (x + t • (v x)))
  have ss_inj : suff_small_inj f := by
    rcases (c1_implies_lipschitz v h.diff) with ⟨K, hK⟩


  sorry




#check volume (ball (0 : E 3) 1)

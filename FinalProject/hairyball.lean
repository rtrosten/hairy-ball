import Mathlib

open RealInnerProductSpace

notation "E" n:30 => EuclideanSpace ℝ (Fin n)



structure IsSphVF {n : ℕ} (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) where
  diff : ContDiff ℝ ⊤ v
  perp : ∀x, ‖x‖ = 1 → ⟪x, v x⟫ = 0

structure IsEqvSphVF {n : ℕ}
  (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) extends IsSphVF v where
  equiv : ∀ r > (0 : ℝ), ∀ x, v (r • x) = r • v x

open Polynomial MeasureTheory Metric ENNReal Topology Set Filter Function

def suff_small_inj (f: ℝ → E n → E n) := ∀ᶠ t in 𝓝 (0:ℝ), Injective (f t)
def suff_small_surj (f: ℝ → E n → E n) := ∀ᶠ t in 𝓝 (0:ℝ), Surjective (f t)
def IsPolynomialFun (f : ℝ → ℝ) := ∃ P : ℝ[X], f = P.eval

example (P Q : ℝ[X]) (h : P.eval = Q.eval) : P = Q := Polynomial.funext (congrFun h)

-- some examples of using ∀ᶠ, thanks Prof. Massot!
example {K : ℝ} (hK : K > 0) : ∀ᶠ t in 𝓝 (0 : ℝ), K*|t| < 1 := by
  have F₁ : ∀ t ∈ Ioo (-(1/K)) (1/K), K*|t| < 1 := by
    intro t ht
    have : |t| < 1/K := abs_lt.mpr ht
    rwa [lt_div_iff' hK] at this
  have F₂ : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-(1/K)) (1/K) := by
    refine Ioo_mem_nhds ?ha ?hb <;> simp [hK]
  exact  F₂.mono F₁


example {K : ℝ} : ∀ᶠ t in 𝓝 (0 : ℝ), K*|t| < 1 := by
  have F₁ : Tendsto (fun t ↦ K*|t|) (𝓝 0) (𝓝 0) := by
    suffices Tendsto (fun t ↦ K*|t|) (𝓝 0) (𝓝 (K*0)) by simpa
    refine Tendsto.const_mul K ?h
    suffices Tendsto (fun t : ℝ ↦ |t|) (𝓝 0) (𝓝 (|0|)) by simpa
    exact continuous_abs.continuousAt
  have F₂ : Iio (1 : ℝ) ∈ 𝓝 0 := Iio_mem_nhds zero_lt_one
  exact F₁.eventually F₂


lemma smooth_imp_c1 (v : E n → E n) (hv : ContDiff ℝ ⊤ v) : ContDiff ℝ 1 v :=
  hv.of_le le_top

lemma c1_implies_lipschitz (v : E n → E n) (hv : ContDiff ℝ ⊤ v) : ∃ K, LipschitzWith K v := by sorry

lemma c1_implies_lipschitz2 (v : E n → E n) (hv : ContDiff ℝ ⊤ v) (A : Set (E n)) (hA : Convex ℝ A) : ∃ K : NNReal, LipschitzWith K (Set.restrict A v) := by

  sorry

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

lemma poly_transform (v : E n → E n) (hv : ContDiff ℝ ⊤ v) (A : Set (E n)) (hA : IsCompact A) :
  ∀ᶠ t in 𝓝 0, (Function.Injective (fun x : A ↦ x + t • (v x)) ∧
  IsPolynomialFun (fun t ↦ volume ((fun x : A ↦ x + t • (v x))'' A))) := sorry

theorem hairy_ball_aux {n} {v : E n → E n} (h : IsEqvSphVF v) (h' : ∀x, ‖x‖ = 1 → v x ≠ 0) : Even n := sorry

theorem hairy_ball {n} {v : E n → E n} (h : IsSphVF v) (h' : ∀x, ‖x‖ = 1 → v x ≠ 0) : Even n := by
  let f : ℝ → E n → E n := fun t ↦ (fun x ↦ (x + t • (v x)))
  have ss_inj : suff_small_inj f := by
    rcases (c1_implies_lipschitz v h.diff) with ⟨K, hK⟩
    have F₁ : ∀ᶠ t in 𝓝 0, ∃C, AntilipschitzWith C (f t) := by
      have G₁ : ∀ x y : E n, ‖f t x - f t y‖ ≥ (1-C|t|) * ‖x-y‖ := by
        sorry
      have G₂ : ∀ᶠ t in 𝓝 (0 : ℝ), K*|t| < 1 := by
        sorry
      exact G₂.mono G₁

  sorry




#check volume (ball (0 : E 3) 1)

import Mathlib

noncomputable section

open RealInnerProductSpace

notation "E" n:30 => EuclideanSpace ℝ (Fin n)



structure IsSphVF {n : ℕ} (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) where
  diff : ContDiff ℝ ⊤ v
  perp : ∀x, ‖x‖ = 1 → ⟪x, v x⟫ = 0

structure IsEqvSphVF {n : ℕ}
  (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) extends IsSphVF v where
  equiv : ∀ r > (0 : ℝ), ∀ x, v (r • x) = r • v x

open Polynomial MeasureTheory Metric ENNReal Topology Set Filter Function

def suff_small_inj {n} (f: ℝ → E n → E n) := ∀ᶠ t in 𝓝 (0:ℝ), Injective (f t)
def suff_small_surj {n} (f: ℝ → E n → E n) := ∀ᶠ t in 𝓝 (0:ℝ), Surjective (f t)
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


lemma smooth_imp_c1 {n} (v : E n → E n) (hv : ContDiff ℝ ⊤ v) : ContDiff ℝ 1 v :=
  hv.of_le le_top

lemma c1_implies_lipschitz {n} (v : E n → E n) (hv : ContDiff ℝ ⊤ v) : ∃ K > 0, LipschitzWith K v := by sorry

lemma c1_implies_lipschitz2 {n} (v : E n → E n) (hv : ContDiff ℝ ⊤ v) (A : Set (E n)) (hA : Convex ℝ A) : ∃ K : NNReal, LipschitzWith K (Set.restrict A v) := by
  sorry

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

-- lemma poly_transform {n} (v : E n → E n) (hv : ContDiff ℝ ⊤ v) (A : Set (E n)) (hA : IsCompact A) :
--   ∀ᶠ t in 𝓝 0, (Function.Injective (fun x : A ↦ x + t • (v x)) ∧
--   IsPolynomialFun (fun t ↦ volume ((fun x : A ↦ x + t • (v x))'' A))) := sorry

theorem hairy_ball_aux {n} {v : E n → E n} (h : IsEqvSphVF v) (h' : ∀x, ‖x‖ = 1 → v x ≠ 0) : Even n := sorry


lemma norm_sub_norm_le'' {F : Type*} [SeminormedAddGroup F] (a b : F) : ‖a‖ - ‖b‖ ≤ ‖a + b‖ := by
  convert norm_sub_norm_le a (-b) using 1 <;> simp

def f {n} (v : E n → E n) (t : ℝ) (x : E n) : E n := x + t • (v x)

lemma f_inj {n} {v : E n → E n} (h : IsSphVF v) : suff_small_inj (f v) := by
  rcases (c1_implies_lipschitz v h.diff) with ⟨K, hK⟩
  have hK₁ := hK.1
  have hK₂ := hK.2
  have F₁ : ∀ᶠ t in 𝓝 (0 : ℝ), ∃C > 0, AntilipschitzWith (C : NNReal) (f v t) := by
    have G₁ : ∀ t, ∀ x y : E n, ‖f v t x - f v t y‖ ≥ (1-(K:ℝ)*|t|) * ‖x-y‖ := by
      intro t x y
      calc
        ‖f v t x - f v t y‖ = ‖x - y + t • (v x - v y)‖ := by congr 1; rw [smul_sub]; dsimp [f]; abel
        _ ≥ ‖x-y‖ - ‖t • (v x - v y)‖ := by apply norm_sub_norm_le''
        _ = ‖x-y‖ - |t| * ‖v x - v y‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≥ ‖x-y‖ - |t| * (K * ‖x-y‖) := by gcongr ; apply hK₂.dist_le_mul
        _ = (1-K*|t|)*‖x-y‖ := by linarith

    have G₂ : ∀ᶠ t in 𝓝 (0 : ℝ), (K:ℝ)*|t| < 1 := by
      have H₁ : ∀ t ∈ Ioo (-(1/(K:ℝ))) (1/(K:ℝ)), K*|t| < 1 := by
        intro t ht
        have : |t| < 1/K := abs_lt.mpr ht
        have hK₁' : (0 : ℝ) < K := by exact_mod_cast hK₁
        rwa [lt_div_iff' hK₁'] at this
      have H₂ : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-(1/(K:ℝ))) (1/(K:ℝ)) := by
        refine Ioo_mem_nhds ?ha ?hb <;> simp [hK]
      exact H₂.mono H₁

    have G₃ : ∀ (t : ℝ), (K:ℝ) * |t| < 1 → 1 - (K:ℝ) * |t| > 0 := by
      intro t ht
      linarith

    have G₄ := G₂.mono G₃

    have G₅ : ∀ (t : ℝ), 1-(K:ℝ) * |t| > 0 → ∃ C > 0, AntilipschitzWith C (f v t) := by
      intro t ht
      use 1/⟨1-K*|t|, ht.le⟩
      constructor
      · exact one_div_pos.mpr ht
      · rw [antilipschitzWith_iff_le_mul_dist]
        peel G₁ t with H y x
        field_simp
        exact (le_div_iff' ht).mpr (G₁ t y x)

    exact G₄.mono G₅

  have F₂ : ∀ t, (∃ C > 0, AntilipschitzWith C (f v t)) → Injective (f v t) := by
    intro t hc
    rcases hc with ⟨c,_,hcc⟩
    apply AntilipschitzWith.injective
    exact hcc

  exact F₁.mono F₂

lemma f_surj {n} {v : E n → E n} (h : IsSphVF v) (hv : ∀ u : E n, ‖u‖ = 1 → ‖v u‖ = 1): ∀ᶠ t in 𝓝 (0 : ℝ), (∀ u : E n, ‖u‖ = 1 → ‖f v t u‖ = Real.sqrt (1 + t^2))
  ∧ (∀ u' : E n, ‖u'‖ = Real.sqrt (1 + t^2) → ∃ u : E n, ‖u‖ = 1 ∧ f v t u = u') := by
  have fact : ∀ t : ℝ, ∀ u : E n, ‖u‖ = 1 → ‖f v t u‖^2 = 1 + t^2 := by
    intro t u hu
    calc ‖f v t u‖^2 = ‖u + t • v u‖^2 := by congr
      _ = ‖u‖^2 + 2 * ⟪u, (t • v u)⟫ + ‖t • v u‖^2 := norm_add_sq_real u (t • v u)
      _ = ‖u‖^2  + ‖t • v u‖^2 := by
        simp [-PiLp.inner_apply, real_inner_smul_right, h.perp _ hu]
      _ = 1 + ‖t • v u‖^2 := by
        rw [hu]
        simp
      _ = 1 + t^2 * ‖v u‖^2 := by
        rw [norm_smul, mul_pow]
        simp
      _ = 1 + t^2 := by
        rw [hv u hu]
        simp
  let g := fun v t x ↦ (1 / (Real.sqrt (1 + t^2))) • (f (n := n) v t x)
  have restrict : g '' {x : E n | ‖x‖ = 1} ⊆ {x : E n | ‖x‖ = 1} := by
  sorry

theorem hairy_ball {n} {v : E n → E n} (h : IsSphVF v) (h' : ∀x, ‖x‖ = 1 → v x ≠ 0) (h'' :
∀ x, ‖v x‖ = 1) : Even n := by
  have ss_inj : suff_small_inj (f v) := f_inj h
  sorry




#check volume (ball (0 : E 3) 1)

import Mathlib

noncomputable section

open RealInnerProductSpace
open Polynomial MeasureTheory Metric ENNReal Topology Set Filter Function

notation "E" n:30 => EuclideanSpace ℝ (Fin n)
notation "S" n:30 "_(" r:10 ")" => Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r


structure IsSphVF {n : ℕ} (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) where
  diff : ContDiff ℝ ⊤ v
  perp : ∀x, ‖x‖ = 1 → ⟪x, v x⟫ = 0

structure IsEqvSphVF {n : ℕ}
  (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) extends IsSphVF v where
  equiv : ∀ r > (0 : ℝ), ∀ x, v (r • x) = r • v x



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

def H {n} (t : ℝ) (x : E n) : E n := t • x

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
  have fact : ∀ t : ℝ, ∀ u : E n, ‖u‖ = 1 → ‖f v t u‖ = Real.sqrt (1 + t^2) := by
    intro t u hu
    have square : ‖f v t u‖^2 = 1 + t^2 := by
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
    have pos1 : 0 ≤ ‖f v t u‖ := by exact norm_nonneg (f v t u)
    have pos2 : 0 ≤ 1 + t^2 := by
      calc 0 ≤ t^2 := sq_nonneg t
        _ ≤ 1 + t^2 := by linarith
    apply Eq.symm
    rw [Real.sqrt_eq_iff_sq_eq pos2 pos1]
    exact square
  let g := fun v t x ↦ (1 / (Real.sqrt (1 + t^2))) • (f (n := n) v t x)
  let g₀ := fun v t ↦ Set.restrict {x : E n | ‖x‖ = 1} (g v t)
  have hg₀ : ∀ t : ℝ, ∀ x : {x : E n | ‖x‖ = 1}, g₀ v t x ∈ {x : E n | ‖x‖ = 1} := by sorry
  let g₁ := fun t ↦ Set.codRestrict (g₀ v t) {x : E n | ‖x‖ = 1} (hg₀ t)

  let h := fun (y : {x : E n | ‖x‖ = 1}) t (x : {x : E n | ‖x‖ = 1}) ↦ Real.sqrt (1 + t^2) • y - t • v x
  have fxd_pt : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y : {x : E n | ‖x‖ = 1}, ∃ x : {x : E n | ‖x‖ = 1}, Function.IsFixedPt (h y t) x
  sorry

lemma annulem {n} : {x : E n | 0.5 ≤ ‖x‖ ∧ ‖x‖ ≤ 1.5} = ⋃ (r ∈ Icc (0.5: ℝ) (1.5: ℝ)), {x : E n | ‖x‖ = r}  := by
  ext y
  constructor
  · intro hy
    dsimp at *
    rw [mem_iUnion]
    simp [hy]
  · intro hy
    rw [mem_iUnion] at hy
    rcases hy with ⟨s, hy⟩
    rw [mem_iUnion] at hy
    rcases hy with ⟨w, hw⟩
    rw [mem_setOf_eq, hw]
    exact w

lemma f_surj_new {n} {v : E n → E n} (h : IsSphVF v) (hv : ∀ x : E n, ‖v x‖ = ‖x‖ ∧ ⟪x, v x⟫ = 0) (hv' : ∀ r : ℝ, ∀ x : E n, v (r • x) = r • v x) : ∀ᶠ t in 𝓝 (0 : ℝ), (∀ u : E n, ‖u‖ = 1 → ‖f v t u‖ = Real.sqrt (1 + t^2))
  ∧ (∀ u' : E n, ‖u'‖ = Real.sqrt (1 + t^2) → ∃ u : E n, ‖u‖ = 1 ∧ f v t u = u') := by
  have norm_lemma : ∀ t : ℝ, ∀ x : E n, ‖x + t • v x‖ = ‖x‖ * Real.sqrt (1 + t^2) := by
    intro t x
    have square : ‖x + t • v x‖^2 = ‖x‖^2 * (1 + t^2) := by
      calc ‖x + t • v x‖^2 = ‖x‖^2 + 2 * ⟪x, (t • v x)⟫ + ‖t • v x‖^2 := norm_add_sq_real x (t • v x)
        _ = ‖x‖^2 + ‖t • v x‖^2 := by
          simp [-PiLp.inner_apply, real_inner_smul_right, (hv x).right]
        _ = ‖x‖^2 + t^2 * ‖v x‖^2 := by
          rw [norm_smul, mul_pow]
          simp
        _ = ‖x‖^2 * (1 + t^2) := by
          rw [mul_comm, (hv x).left]
          exact (mul_one_add (‖x‖ ^ 2) (t ^ 2)).symm
    have pos1 : 0 ≤ ‖x + t • v x‖ := by exact norm_nonneg (x + t • v x)
    have pos2 : 0 ≤ ‖x‖^2 * (1 + t^2) := by
      have pos3 : 0 ≤ 1 + t^2 := calc 0 ≤ t^2 := sq_nonneg t
          _ ≤ 1 + t^2 := by linarith
      exact mul_nonneg (sq_nonneg ‖x‖) pos3
    calc ‖x + t • v x‖ = Real.sqrt (‖x‖^2 * (1 + t^2)) := ((fun {x y} hx hy ↦ (Real.sqrt_eq_iff_sq_eq hx hy).mpr) pos2 pos1 square).symm
      _ = Real.sqrt (‖x‖^2) * Real.sqrt (1 + t^2) := by
        refine Real.sqrt_mul (sq_nonneg ‖x‖) (1 + t ^ 2)
      _ = ‖x‖ * Real.sqrt (1 + t^2) := by
        congr
        refine Real.sqrt_sq (norm_nonneg x)
  have first : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u : E n, ‖u‖ = 1 → ‖f v t u‖ = Real.sqrt (1 + t^2) := by
    have fact : ∀ t : ℝ, ∀ u : E n, ‖u‖ = 1 → ‖f v t u‖ = Real.sqrt (1 + t^2) := by
      intro t u hu
      unfold f
      rw [norm_lemma t u]
      simp [hu]
    sorry
  have second : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u' : E n, ‖u'‖ = Real.sqrt (1 + t^2) → ∃ u : E n, ‖u‖ = 1 ∧ f v t u = u' := by
    have LipCst : ∃ K > 0, LipschitzWith K (Set.restrict {x : E n | 1/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3/2} v) := by sorry
    rcases LipCst with ⟨K, hvK⟩
    have point : ∀ t : ℝ, |t| < 1/3 ∧ |t| < 1/K → ∀ u' : E n, ‖u'‖ = Real.sqrt (1 + t^2) → ∃ u : E n, ‖u‖ = 1 ∧ f v t u = u' := by
      intro t ht u' hu'
      have hu'' : ‖u'‖ = |Real.sqrt (1 + t^2)| := by
        rw [hu']
        exact (LatticeOrderedGroup.abs_of_nonneg (Real.sqrt (1 + t^2)) (Real.sqrt_nonneg (1 + t ^ 2))).symm
      have calculation : |1/(Real.sqrt (1 + t^2))| * |Real.sqrt (1 + t^2)| = 1 := by
        rw [abs_one_div (Real.sqrt (1 + t^2))]
        dsimp -- lmao no way i'm stuck on this
        sorry
      unfold f
      let A := {x : E n | 1/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3/2}
      let g := fun x : {x : E n | 1/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3/2} ↦ (1/(Real.sqrt (1 + t^2))) • u' - t • v x
      have restr : ∀ x : {x : E n | 1/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3/2}, g x ∈ {x : E n | 1/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3/2} := by
        intro x
        have : |t| * ‖(x : E n)‖ ≤ 1/2 := by
          calc |t| * ‖(x : E n)‖ ≤ 1/3 * 3/2 := by sorry
            _ = 1/2 := by ring
        have : 1 - 1/2 ≤ 1 - |t| * ‖(x : E n)‖ := by
          sorry
        constructor
        · dsimp
          calc 1/2 = 1 - 1/2 := by ring
            _ ≤ |1/(Real.sqrt (1 + t^2))| * ‖u'‖ - |t| * ‖(x : E n)‖ := by
              rw [hu'', calculation]
              exact this
            _ = ‖(1/(Real.sqrt (1 + t^2))) • u'‖ - ‖t • v x‖ := by
              congr
              sorry
            _ ≤ |‖(1/(Real.sqrt (1 + t^2))) • u'‖ - ‖t • v x‖| := le_abs_self (‖(1 / Real.sqrt (1 + t ^ 2)) • u'‖ - ‖t • v ↑x‖)
            _ ≤ ‖(1/(Real.sqrt (1 + t^2))) • u' - t • v x‖ := by apply abs_norm_sub_norm_le
        · dsimp
          calc ‖(1 / Real.sqrt (1 + t ^ 2)) • u' - t • v ↑x‖ ≤ ‖(1 / Real.sqrt (1 + t ^ 2)) • u'‖ + ‖t • v ↑x‖ := by sorry
            _ ≤ 1 + t * ‖(x : E n)‖ := by sorry
            _ ≤ 3/2 := by sorry
      let h := fun z ↦ (Set.codRestrict g {x : E n | 1/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3/2} restr z)
      have complete : IsComplete {x : E n | 1/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3/2} := by
        sorry
      have key : ∃ u, Function.IsFixedPt h u := by sorry
      rcases key with ⟨u, hu⟩
      use u
      have key' : u + t • v u = u' := by sorry
      constructor
      · have fact₀ : 1 + t^2 = ‖(u : E n)‖^2 * (1 + t^2) := by sorry
        have fact₁ : 1 = ‖(u : E n)‖ := by sorry
        rw [fact₁]
      · exact key'
    sorry

  exact first.and second



theorem hairy_ball {n} {v : E n → E n} (h : IsSphVF v) (h' : ∀x, ‖x‖ = 1 → v x ≠ 0) (h'' :
∀ x, ‖x‖ = 1 → ‖v x‖ = 1) : Even n := by
  have ss_inj : suff_small_inj (f v) := f_inj h
  have ss_surj := f_surj h h''
  sorry



#check volume (ball (0 : E 3) 1)

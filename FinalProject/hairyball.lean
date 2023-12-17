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

@[simp]
lemma srqt_pos (t : ℝ) : 0 < Real.sqrt (1 + t^2) := by
  refine Real.sqrt_pos.mpr ?_ -- suggested by apply?
  positivity -- gets rid of obvious positivity goals.

open Real

lemma norm_f {n} {v : E n → E n} (hv : ∀ x : E n, ‖v x‖ = ‖x‖ ∧ ⟪x, v x⟫ = 0) (t : ℝ) (x : E n) :
    ‖f v t x‖ = ‖x‖ * sqrt (1 + t^2) := by
  have square : ‖x + t • v x‖^2 = ‖x‖^2 * (1 + t^2) := by
    calc ‖x + t • v x‖^2 = ‖x‖^2 + 2 * ⟪x, (t • v x)⟫ + ‖t • v x‖^2 := norm_add_sq_real x (t • v x)
      _ = ‖x‖^2 + ‖t • v x‖^2 := by simp [-PiLp.inner_apply, real_inner_smul_right, (hv x).right]
      _ = ‖x‖^2 + t^2 * ‖x‖^2 := by simp [norm_smul, mul_pow, (hv x).left]
      _ = ‖x‖^2 * (1 + t^2) := by ring
  calc ‖x + t • v x‖ = sqrt (‖x‖^2 * (1 + t^2)) := by rw [eq_comm, sqrt_eq_iff_sq_eq, square] <;> positivity
    _ = sqrt (‖x‖^2) * sqrt (1 + t^2) := by apply sqrt_mul; positivity
    _ = ‖x‖ * sqrt (1 + t^2) := by rw [sqrt_sq]; positivity

lemma norm_f_on_sphere {n} {v : E n → E n} (hv : ∀ x : E n, ‖v x‖ = ‖x‖ ∧ ⟪x, v x⟫ = 0)
    (t : ℝ) (u : E n) (hu : ‖u‖ = 1) : ‖f v t u‖ = sqrt (1 + t^2) := by
  simp [norm_f hv t u, hu]

lemma f_surj {n} {v : E n → E n} (h : IsSphVF v) (hv : ∀ x : E n, ‖v x‖ = ‖x‖ ∧ ⟪x, v x⟫ = 0) (hv' : ∀ r : ℝ, ∀ x : E n, v (r • x) = r • v x) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u' : E n, ‖u'‖ = sqrt (1 + t^2) → ∃ u : E n, ‖u‖ = 1 ∧ f v t u = u' := by
  have LipCst : ∃ K > 0, LipschitzWith K (Set.restrict {x : E n | 1/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3/2} v) := by sorry -- This is that Lip on compact thing
  rcases LipCst with ⟨K, hvK⟩
  have point : ∀ t : ℝ, |t| < 1/3 ∧ |t| < 1/K → ∀ u' : E n, ‖u'‖ = sqrt (1 + t^2) → ∃ u : E n, ‖u‖ = 1 ∧ f v t u = u' := by
    intro t ht u' hu'
    have hu'' : ‖u'‖ = |sqrt (1 + t^2)| := by
      rw [hu']
      exact (LatticeOrderedGroup.abs_of_nonneg (sqrt (1 + t^2)) (sqrt_nonneg (1 + t ^ 2))).symm
    have calculation : |1/(sqrt (1 + t^2))| * |sqrt (1 + t^2)| = 1 := by
      field_simp [abs_one_div]
    unfold f
    let A := {x : E n | 1/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3/2}

    have complete : IsComplete A := by
      apply IsClosed.isComplete
      have h_1 : IsClosed {x : E n | 1/2 ≤ ‖x‖} := by sorry
      have h_2 : IsClosed {x : E n | ‖x‖ ≤ 3/2} := by sorry
      apply IsClosed.inter h_1 h_2
    let g₀ := fun x : E n ↦ (1/(sqrt (1 + t^2))) • u' - t • v x
    have hg₀ : Set.MapsTo g₀ A A := by
      intro x hx
      have : |t| * ‖(x : E n)‖ ≤ 1/2 := by
        calc |t| * ‖(x : E n)‖ ≤ 1/3 * 3/2 := by sorry
          _ = 1/2 := by ring
      have : 1 - 1/2 ≤ 1 - |t| * ‖(x : E n)‖ := by
        sorry
      constructor
      · dsimp
        calc 1/2 = 1 - 1/2 := by ring
          _ ≤ |1/(sqrt (1 + t^2))| * ‖u'‖ - |t| * ‖(x : E n)‖ := by
            rw [hu'', calculation]
            exact this
          _ = ‖(1/(sqrt (1 + t^2))) • u'‖ - ‖t • v x‖ := by
            rw [norm_smul, norm_smul, (hv x).1] ; rfl
          _ ≤ |‖(1/(sqrt (1 + t^2))) • u'‖ - ‖t • v x‖| := le_abs_self (‖(1 / sqrt (1 + t ^ 2)) • u'‖ - ‖t • v ↑x‖)
          _ ≤ ‖(1/(sqrt (1 + t^2))) • u' - t • v x‖ := by apply abs_norm_sub_norm_le
      · dsimp
        calc ‖(1 / sqrt (1 + t ^ 2)) • u' - t • v ↑x‖ ≤ ‖(1 / sqrt (1 + t ^ 2)) • u'‖ + ‖t • v ↑x‖ := by sorry
          _ ≤ 1 + t * ‖(x : E n)‖ := by sorry
          _ ≤ 3/2 := by sorry
    have pos : 0 ≤ |t| * (K : ℝ) := by sorry
    have pos' : Real.toNNReal (|t| * (K : ℝ)) = |t| * (K : ℝ) := Real.coe_toNNReal (|t| * (K : ℝ)) pos
    have contract : ContractingWith (Real.toNNReal (|t| * (K : ℝ))) (Set.MapsTo.restrict g₀ A A hg₀) := by
      constructor
      · sorry
      · intro x y
        have simplify₀ : edist (MapsTo.restrict g₀ A A hg₀ x) (MapsTo.restrict g₀ A A hg₀ y) = ENNReal.ofReal ‖g₀ x - g₀ y‖ := by sorry
        have simplify₁ : ENNReal.toReal (ENNReal.ofReal ‖g₀ x - g₀ y‖) = ‖g₀ x - g₀ y‖ := by sorry
        rw [simplify₀]
        have key : ‖g₀ x - g₀ y‖ ≤ |t| * (K : ℝ) * ‖(x : E n) - (y : E n)‖ := by
          calc ‖g₀ x - g₀ y‖ = ‖((1/(sqrt (1 + t^2))) • u' - t • v x) - ((1/(sqrt (1 + t^2))) • u' - t • v y)‖ := by rfl
            _ = ‖t • v y - t • v x‖ := by simp
            _ = ‖t • (v y - v x)‖ := by
              rw [smul_sub]
            _ = |t| * ‖v y - v x‖ := by
              rw [norm_smul, Real.norm_eq_abs]
            _ = |t| * ((K : ℝ) * ‖(y : E n) - (x : E n)‖) := by
              --have weird : ENNReal.toReal ⟨‖(y : E n) - (x : E n)‖, norm_nonneg (y - x)⟩ = edist y x := by sorry
              sorry -- very, very stuck on how to make this work
            _ = |t| * (K : ℝ) * ‖(x : E n) - (y : E n)‖ := by
              rw [mul_assoc]
              simp
              left
              left
              rw [← norm_neg]
              congr
              abel
          sorry
        sorry
    have duh : ∃ x, x ∈ A := by sorry
    rcases duh with ⟨p, hp⟩
    have findist : edist p (g₀ p) ≠ ⊤ := edist_ne_top p (g₀ p)
    have key : ∃ u, Function.IsFixedPt g₀ u := by
      have banach := ContractingWith.exists_fixedPoint' complete hg₀ contract hp findist
      rcases banach with ⟨u, hu⟩
      use u
      exact hu.right.left
    rcases key with ⟨u, hu⟩
    use (sqrt (1 + t^2)) • u
    have key' : (sqrt (1 + t^2)) • u + t • v ((sqrt (1 + t^2)) • u) = u' := by
      unfold IsFixedPt at hu
      have comp₀ : (1/(sqrt (1 + t^2))) • u' - t • v u = u := hu
      have comp₁ : u' - t • v ((sqrt (1 + t^2)) • u) = (sqrt (1 + t^2)) • u := by
        calc u' - t • v ((sqrt (1 + t^2)) • u) = u' - t • ((sqrt (1 + t^2)) • v u) := by rw [hv' (sqrt (1 + t^2)) u]
          _ = u' - (sqrt (1 + t^2)) • (t • v u) := by
            simp
            exact smul_algebra_smul_comm (sqrt (1 + t ^ 2)) t (v u)
          _ = (sqrt (1 + t^2)) • ((1/(sqrt (1 + t^2))) • u' - t • v u) := by
            rw [smul_sub]
            simp
            refine (smul_inv_smul₀ ?hc u').symm
            have contra : sqrt (1 + t^2) > 0 := by
              rw [gt_iff_lt, sqrt_pos]
              calc 0 < 1 := Real.zero_lt_one
                _ ≤ 1 + t^2 := by refine le_add_of_nonneg_right (sq_nonneg t)
            exact ne_of_gt contra
          _ = (sqrt (1 + t^2)) • u := by rw [comp₀]
      nth_rw 1 [← comp₁]
      simp
    constructor
    · have comp := by
        calc 1 + t^2 = (sqrt (1 + t^2))^2 := by {
          rw [Real.sq_sqrt ?_]
          calc 0 ≤ 1 := zero_le_one
            _ ≤ 1 + t^2 := by refine le_add_of_nonneg_right (sq_nonneg t)
        }
          _ = ‖u'‖^2 := by rw [hu']
          _ = ‖sqrt (1 + t ^ 2) • u + t • v (sqrt (1 + t ^ 2) • u)‖^2 := by rw [key']
          _ = ‖sqrt (1 + t ^ 2) • u + t • ((sqrt (1 + t ^ 2)) • v u)‖^2 := by rw [hv' (sqrt (1 + t ^ 2)) u]
          _ = ‖sqrt (1 + t ^ 2) • u + (sqrt (1 + t ^ 2)) • (t • v u)‖^2 := by rw [smul_algebra_smul_comm (sqrt (1 + t ^ 2)) t (v u)]
          _ = ‖sqrt (1 + t^2) • (u + (t • v u))‖^2 := by rw[smul_add]
          _ = (sqrt (1 + t^2) * ‖u + t • v u‖)^2 := by
            congr
            apply norm_smul_of_nonneg (sqrt_nonneg (1 + t^2)) (u + t • v u)
          _ = (sqrt (1 + t^2))^2 * ‖u + t • v u‖^2 := by rw[mul_pow]
          _ = (1 + t^2) * ‖u + t • v u‖^2 := by
            congr
            refine Real.sq_sqrt ?_
            calc 0 ≤ 1 := zero_le_one
              _ ≤ 1 + t^2 := by refine le_add_of_nonneg_right (sq_nonneg t)
          _ = (1 + t^2) * (‖u‖ * sqrt (1 + t^2))^2 := by sorry
          _ = (1 + t^2) * (sqrt (1 + t^2) * ‖u‖)^2 := by
            rw [mul_comm (sqrt (1 + t^2)) ‖u‖]
          _ = (1 + t^2) * (‖sqrt (1 + t^2) • u‖)^2 := by
            congr
            rw [norm_smul_of_nonneg (sqrt_nonneg (1 + t^2)) u]
      have duh : 1 + t^2 ≠ 0 := by sorry
      rw [left_eq_mul₀ duh, sq_eq_one_iff] at comp
      rcases comp with h1 | h2
      · exact h1
      · exfalso
        have bad : 0 ≤ (-1 : ℝ) := by
          rw [← h2]
          exact norm_nonneg ((sqrt (1 + t^2)) • u)
        linarith
    · exact key'
  sorry

theorem hairy_ball {n} {v : E n → E n} (h : IsSphVF v) (h' : ∀x, ‖x‖ = 1 → v x ≠ 0) (h'' :
∀ x, ‖x‖ = 1 → ‖v x‖ = 1) : Even n := by
  have ss_inj : suff_small_inj (f v) := f_inj h
  sorry



#check volume (ball (0 : E 3) 1)

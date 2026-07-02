import Mathlib

/-!
# Finite subsets of `ℝ` have `q`-negative type for `0 < q ≤ 2`

A metric space `(X, d)` has *`q`-negative type* if for every finite collection of
points `x₁, …, xₙ ∈ X` and reals `c₁, …, cₙ` with `∑ cᵢ = 0` one has
`∑ᵢ ∑ⱼ cᵢ cⱼ d(xᵢ, xⱼ)^q ≤ 0`.

We prove that every finite subset `S ⊆ ℝ`, with the usual metric `d x y = |x - y|`,
has `q`-negative type for all `0 < q ≤ 2`.

The proof uses the integral representation, valid for `0 < q < 2`,
`|t|^q = (1/K) ∫_{(0,∞)} (1 - cos (t s)) / s^{1+q} ds`,
where `K = ∫_{(0,∞)} (1 - cos s)/s^{1+q} ds > 0`, together with the pointwise
nonpositivity `∑ᵢⱼ cᵢ cⱼ (1 - cos ((xᵢ - xⱼ) s)) ≤ 0` (a sum of two squares with a sign).
The endpoint `q = 2` is purely algebraic.
-/

open MeasureTheory Set

namespace NegType

/-- The radial kernel `g q u = (1 - cos u) / u ^ (1 + q)`. -/
noncomputable def g (q : ℝ) (u : ℝ) : ℝ := (1 - Real.cos u) / u ^ (1 + q)

/-- The normalising constant `K q = ∫_{(0,∞)} (1 - cos u)/u^{1+q} du`. -/
noncomputable def Kconst (q : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), g q u

lemma g_nonneg (q : ℝ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ g q u :=
  div_nonneg (sub_nonneg.mpr (Real.cos_le_one u)) (Real.rpow_nonneg hu _)

/-- The kernel `(1 - cos (t s)) / s ^ (1 + q)` is integrable on `(0, ∞)` for `0 < q < 2`. -/
lemma integrable_kern {q : ℝ} (hq0 : 0 < q) (hq2 : q < 2) (t : ℝ) :
    IntegrableOn (fun s => (1 - Real.cos (t * s)) / s ^ (1 + q)) (Ioi 0) := by
  have hmeas : Measurable fun s : ℝ => (1 - Real.cos (t * s)) / s ^ (1 + q) := by
    fun_prop
  -- Near `0`: `1 - cos (t s) ≤ (t s)²/2`, and `s ^ (1 - q)` is integrable since `1 - q > -1`.
  have h01 : IntegrableOn (fun s => (1 - Real.cos (t * s)) / s ^ (1 + q)) (Ioc 0 1) := by
    refine ((intervalIntegral.intervalIntegrable_rpow'
      (show (-1 : ℝ) < 1 - q by linarith)).1.const_mul
        (t ^ 2 / 2)).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hcos : |1 - Real.cos (t * s)| ≤ t ^ 2 / 2 * s ^ 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := t * s)]
    calc ‖(1 - Real.cos (t * s)) / s ^ (1 + q)‖
        = |1 - Real.cos (t * s)| / s ^ (1 + q) := by
          rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg hs.1.le _)]
      _ ≤ t ^ 2 / 2 * s ^ 2 / s ^ (1 + q) :=
          div_le_div_of_nonneg_right hcos (Real.rpow_nonneg hs.1.le _)
      _ = t ^ 2 / 2 * s ^ (1 - q) := by
          rw [show (1 : ℝ) - q = 2 - (1 + q) by ring, Real.rpow_sub hs.1]
          norm_cast
          ring
  -- Away from `0`: the numerator is at most `2`, and `s ^ (-(1 + q))` is integrable.
  have h1i : IntegrableOn (fun s => (1 - Real.cos (t * s)) / s ^ (1 + q)) (Ioi 1) := by
    refine ((integrableOn_Ioi_rpow_of_lt (show -(1 + q) < -1 by linarith)
      zero_lt_one).integrable.const_mul 2).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := zero_lt_one.trans hs
    calc ‖(1 - Real.cos (t * s)) / s ^ (1 + q)‖
        = (1 - Real.cos (t * s)) / s ^ (1 + q) :=
          Real.norm_of_nonneg (div_nonneg (sub_nonneg.mpr (Real.cos_le_one _))
            (Real.rpow_nonneg hs0.le _))
      _ ≤ 2 / s ^ (1 + q) :=
          div_le_div_of_nonneg_right (by nlinarith [Real.neg_one_le_cos (t * s)])
            (Real.rpow_nonneg hs0.le _)
      _ = 2 * s ^ (-(1 + q)) := by rw [Real.rpow_neg hs0.le, div_eq_mul_inv]
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  exact h01.union h1i

/-- The basic kernel `g q` is integrable on `(0, ∞)` (the `t = 1` case). -/
lemma integrable_g {q : ℝ} (hq0 : 0 < q) (hq2 : q < 2) :
    IntegrableOn (g q) (Ioi 0) := by
  have h := integrable_kern hq0 hq2 1
  simp only [one_mul] at h
  exact h

/-- Scaling: `∫_{(0,∞)} (1 - cos (t s))/s^{1+q} ds = |t|^q * K q`. -/
lemma integral_kern_eq {q : ℝ} (hq0 : 0 < q) (t : ℝ) :
    (∫ s in Ioi (0 : ℝ), (1 - Real.cos (t * s)) / s ^ (1 + q)) = |t| ^ q * Kconst q := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [Real.zero_rpow hq0.ne']
  have habs : (0 : ℝ) < |t| := abs_pos.mpr ht
  -- Substitute `u = |t| s`.
  have hsub : ∫ s in Ioi (0 : ℝ), g q (|t| * s) = |t|⁻¹ * Kconst q := by
    rw [integral_comp_mul_left_Ioi (g q) 0 habs, mul_zero, smul_eq_mul, Kconst]
  calc ∫ s in Ioi (0 : ℝ), (1 - Real.cos (t * s)) / s ^ (1 + q)
      = ∫ s in Ioi (0 : ℝ), |t| ^ (1 + q) * g q (|t| * s) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        have hcos : Real.cos (|t| * s) = Real.cos (t * s) := by
          rcases abs_choice t with h | h <;> simp [h]
        have h1 : s ^ (1 + q) ≠ 0 := (Real.rpow_pos_of_pos hs.out _).ne'
        have h2 : |t| ^ (1 + q) ≠ 0 := (Real.rpow_pos_of_pos habs _).ne'
        simp only [g]
        rw [Real.mul_rpow habs.le hs.out.le, hcos]
        field_simp
    _ = |t| ^ (1 + q) * (|t|⁻¹ * Kconst q) := by rw [integral_const_mul, hsub]
    _ = |t| ^ q * Kconst q := by
        rw [← mul_assoc, ← Real.rpow_neg_one |t|, ← Real.rpow_add habs,
          show (1 : ℝ) + q + -1 = q by ring]

/-- The normalising constant is strictly positive. -/
lemma Kconst_pos {q : ℝ} (hq0 : 0 < q) (hq2 : q < 2) : 0 < Kconst q := by
  -- `g q` is positive on `(0, 1)`, so its integral there is positive.
  have hpos : 0 < ∫ u in Ioo (0 : ℝ) 1, g q u := by
    have hne : ∀ u ∈ Ioo (0 : ℝ) 1, g q u ≠ 0 := by
      intro u hu
      have hsin : 0 < Real.sin u :=
        Real.sin_pos_of_pos_of_lt_pi hu.1 (by linarith [Real.pi_gt_three, hu.2])
      have hcos : Real.cos u < 1 := by nlinarith [Real.sin_sq_add_cos_sq u]
      exact (div_pos (by linarith) (Real.rpow_pos_of_pos hu.1 _)).ne'
    refine (integral_pos_iff_support_of_nonneg_ae ?_ ?_).mpr ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu using g_nonneg q hu.1.le
    · exact (integrable_g hq0 hq2).mono_set Ioo_subset_Ioi_self
    · rw [Measure.restrict_apply' measurableSet_Ioo]
      refine lt_of_lt_of_le ?_ (measure_mono fun u hu => ⟨hne u hu, hu⟩)
      norm_num [Real.volume_Ioo]
  refine hpos.trans_le (setIntegral_mono_set (integrable_g hq0 hq2) ?_ ?_)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu using g_nonneg q hu.out.le
  · exact ae_of_all _ fun u hu => hu.1

/-- Pointwise nonpositivity of the kernel sum: for weights summing to zero,
`∑ₓ ∑ᵧ c x * c y * (1 - cos ((x - y) s)) ≤ 0`. -/
lemma pointwise_nonpos (S : Finset ℝ) (c : ℝ → ℝ) (hc : ∑ x ∈ S, c x = 0) (s : ℝ) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * (1 - Real.cos ((x - y) * s)) ≤ 0 := by
  -- The quadratic form is `(∑ c)² - (∑ c cos)² - (∑ c sin)²`, and the first square vanishes.
  have key : ∑ x ∈ S, ∑ y ∈ S, c x * c y * (1 - Real.cos ((x - y) * s))
      = (∑ x ∈ S, c x) ^ 2 - ((∑ x ∈ S, c x * Real.cos (x * s)) ^ 2
        + (∑ x ∈ S, c x * Real.sin (x * s)) ^ 2) := by
    have expand : ∀ x y : ℝ, c x * c y * (1 - Real.cos ((x - y) * s))
        = c x * c y - ((c x * Real.cos (x * s)) * (c y * Real.cos (y * s))
          + (c x * Real.sin (x * s)) * (c y * Real.sin (y * s))) := by
      intro x y
      rw [sub_mul, Real.cos_sub]
      ring
    simp only [expand, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul_sum, pow_two]
  rw [key, hc]
  have h1 := sq_nonneg (∑ x ∈ S, c x * Real.cos (x * s))
  have h2 := sq_nonneg (∑ x ∈ S, c x * Real.sin (x * s))
  linarith

/-- Negative type for `0 < q < 2`, via the integral representation. -/
lemma neg_type_lt_two {q : ℝ} (hq0 : 0 < q) (hq2 : q < 2)
    (S : Finset ℝ) (c : ℝ → ℝ) (hc : ∑ x ∈ S, c x = 0) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * |x - y| ^ q ≤ 0 := by
  have hint : ∀ x ∈ S, ∀ y ∈ S, IntegrableOn
      (fun s => c x * c y * ((1 - Real.cos ((x - y) * s)) / s ^ (1 + q))) (Ioi 0) :=
    fun x _ y _ => (integrable_kern hq0 hq2 (x - y)).integrable.const_mul _
  -- Express the quadratic form as an integral against the kernel.
  have hswap : ∫ s in Ioi (0 : ℝ), ∑ x ∈ S, ∑ y ∈ S,
      c x * c y * ((1 - Real.cos ((x - y) * s)) / s ^ (1 + q))
      = ∑ x ∈ S, ∑ y ∈ S, c x * c y * ∫ s in Ioi (0 : ℝ),
          (1 - Real.cos ((x - y) * s)) / s ^ (1 + q) := by
    rw [integral_finsetSum _ fun x hx => integrable_finsetSum _ fun y hy => hint x hx y hy]
    exact Finset.sum_congr rfl fun x hx => by
      rw [integral_finsetSum _ fun y hy => hint x hx y hy]
      exact Finset.sum_congr rfl fun y _ => integral_const_mul _ _
  have hsum : ∑ x ∈ S, ∑ y ∈ S, c x * c y * |x - y| ^ q
      = (∫ s in Ioi (0 : ℝ), ∑ x ∈ S, ∑ y ∈ S,
          c x * c y * ((1 - Real.cos ((x - y) * s)) / s ^ (1 + q))) / Kconst q := by
    rw [hswap, eq_div_iff (Kconst_pos hq0 hq2).ne', Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by rw [integral_kern_eq hq0, mul_assoc]
  -- The integrand is pointwise nonpositive, hence so is the quadratic form.
  rw [hsum]
  refine div_nonpos_of_nonpos_of_nonneg
    (setIntegral_nonpos measurableSet_Ioi fun s hs => ?_) (Kconst_pos hq0 hq2).le
  calc ∑ x ∈ S, ∑ y ∈ S, c x * c y * ((1 - Real.cos ((x - y) * s)) / s ^ (1 + q))
      = (∑ x ∈ S, ∑ y ∈ S, c x * c y * (1 - Real.cos ((x - y) * s))) / s ^ (1 + q) := by
        simp only [Finset.sum_div, mul_div_assoc]
    _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (pointwise_nonpos S c hc s)
        (Real.rpow_nonneg hs.out.le _)

/-- Negative type for the endpoint `q = 2`, algebraically. -/
lemma neg_type_two (S : Finset ℝ) (c : ℝ → ℝ) (hc : ∑ x ∈ S, c x = 0) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * |x - y| ^ (2 : ℝ) ≤ 0 := by
  have key : ∑ x ∈ S, ∑ y ∈ S, c x * c y * (x - y) ^ 2 = -2 * (∑ x ∈ S, c x * x) ^ 2 := by
    have expand : ∀ x, ∑ y ∈ S, c x * c y * (x - y) ^ 2
        = c x * x ^ 2 * ∑ y ∈ S, c y - 2 * (c x * x) * ∑ y ∈ S, c y * y
          + c x * ∑ y ∈ S, c y * y ^ 2 := by
      intro x
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    have h1 : ∑ x ∈ S, c x * x ^ 2 * ∑ y ∈ S, c y = 0 := by simp [hc]
    have h2 : ∑ x ∈ S, c x * ∑ y ∈ S, c y * y ^ 2 = 0 := by
      rw [← Finset.sum_mul, hc, zero_mul]
    have h3 : ∑ x ∈ S, 2 * (c x * x) * ∑ y ∈ S, c y * y = 2 * (∑ x ∈ S, c x * x) ^ 2 := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, sq, mul_assoc]
    calc ∑ x ∈ S, ∑ y ∈ S, c x * c y * (x - y) ^ 2
        = ∑ x ∈ S, (c x * x ^ 2 * ∑ y ∈ S, c y - 2 * (c x * x) * ∑ y ∈ S, c y * y
            + c x * ∑ y ∈ S, c y * y ^ 2) := Finset.sum_congr rfl fun x _ => expand x
      _ = -2 * (∑ x ∈ S, c x * x) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3]
          ring
  calc ∑ x ∈ S, ∑ y ∈ S, c x * c y * |x - y| ^ (2 : ℝ)
      = ∑ x ∈ S, ∑ y ∈ S, c x * c y * (x - y) ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    _ = -2 * (∑ x ∈ S, c x * x) ^ 2 := key
    _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)

/-- **Every finite subset of `ℝ` has `q`-negative type for `0 < q ≤ 2`.**
For a finite set `S ⊆ ℝ` and weights `c : ℝ → ℝ` summing to zero on `S`,
`∑ₓ∈S ∑ᵧ∈S c x * c y * |x - y|^q ≤ 0`. -/
theorem real_finite_negative_type {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2)
    (S : Finset ℝ) (c : ℝ → ℝ) (hc : ∑ x ∈ S, c x = 0) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * |x - y| ^ q ≤ 0 := by
  obtain h | rfl := hq2.lt_or_eq
  · exact neg_type_lt_two hq0 h S c hc
  · exact neg_type_two S c hc

end NegType

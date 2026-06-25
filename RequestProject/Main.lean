import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

open MeasureTheory Set

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace NegType

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

/-- The radial kernel `g q u = (1 - cos u) / u ^ (1 + q)`. -/
noncomputable def g (q : ℝ) (u : ℝ) : ℝ := (1 - Real.cos u) / u ^ (1 + q)

/-- The normalising constant `K q = ∫_{(0,∞)} (1 - cos u)/u^{1+q} du`. -/
noncomputable def Kconst (q : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), g q u

/-
The kernel `(1 - cos (t s)) / s ^ (1 + q)` is integrable on `(0, ∞)`,
for `0 < q < 2`.
-/
lemma integrable_kern {q : ℝ} (hq0 : 0 < q) (hq2 : q < 2) (t : ℝ) :
    IntegrableOn (fun s => (1 - Real.cos (t * s)) / s ^ (1 + q)) (Ioi 0) := by
  -- Split the integral into two parts: from 0 to 1 and from 1 to ∞.
  have h_split : MeasureTheory.IntegrableOn (fun s => (1 - Real.cos (t * s)) / s ^ (1 + q)) (Set.Ioc (0 : ℝ) 1) ∧ MeasureTheory.IntegrableOn (fun s => (1 - Real.cos (t * s)) / s ^ (1 + q)) (Set.Ioi (1 : ℝ)) := by
    constructor;
    · -- For $s \in (0, 1]$, we have $|1 - \cos(ts)| \leq \frac{(ts)^2}{2}$.
      have h_bound : ∀ s ∈ Set.Ioc 0 1, abs ((1 - Real.cos (t * s)) / s ^ (1 + q)) ≤ (t^2 / 2) * s^(1 - q) := by
        -- Using the fact that $|1 - \cos(ts)| \leq \frac{(ts)^2}{2}$ for all $s$, we get:
        have h_bound : ∀ s ∈ Set.Ioc 0 1, abs (1 - Real.cos (t * s)) ≤ (t^2 / 2) * s^2 := by
          intro s hs
          rw [abs_of_nonneg (sub_nonneg_of_le (Real.cos_le_one _))]
          nlinarith [Real.one_sub_sq_div_two_le_cos (x := t * s)]
        intro s hs
        calc
          abs ((1 - Real.cos (t * s)) / s ^ (1 + q))
              = abs (1 - Real.cos (t * s)) / s ^ (1 + q) := by
                rw [abs_div, abs_of_nonneg (Real.rpow_nonneg hs.1.le _)]
          _ ≤ ((t^2 / 2) * s^2) / s ^ (1 + q) :=
                div_le_div_of_nonneg_right (h_bound s hs) (Real.rpow_nonneg hs.1.le _)
          _ = (t^2 / 2) * s^(1 - q) := by
                rw [show 1 - q = 2 - (1 + q) by ring, Real.rpow_sub hs.1]
                norm_cast
                ring
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun s => t ^ 2 / 2 * s ^ ( 1 - q );
      · exact ( intervalIntegral.intervalIntegrable_rpow' ( by linarith ) ).1.const_mul _;
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_const.sub ( Real.continuous_cos.measurable.comp ( measurable_const.mul measurable_id' ) ) ) ( measurable_id'.pow_const _ |> Measurable.inv ) );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with s hs using h_bound s hs;
    · -- For $s \geq 1$, we have $|1 - \cos(ts)| \leq 2$, so we can bound the integrand.
      have h_bound : ∀ s ∈ Set.Ioi (1 : ℝ), abs ((1 - Real.cos (t * s)) / s ^ (1 + q)) ≤ 2 * s ^ (-(1 + q)) := by
        intro s hs; rw [ abs_of_nonneg ( div_nonneg ( sub_nonneg.2 ( Real.cos_le_one _ ) ) ( Real.rpow_nonneg ( by linarith [ Set.mem_Ioi.1 hs ] ) _ ) ) ] ; rw [ Real.rpow_neg ( by linarith [ Set.mem_Ioi.1 hs ] ) ] ; ring_nf;
        nlinarith [ Real.neg_one_le_cos ( t * s ), Real.cos_le_one ( t * s ), inv_pos.mpr ( Real.rpow_pos_of_pos ( zero_lt_one.trans hs ) ( 1 + q ) ) ];
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun s => 2 * s ^ ( - ( 1 + q ) );
      · exact ( integrableOn_Ioi_rpow_of_lt ( by linarith ) ( by linarith ) ) |> fun h => h.const_mul _;
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_const.sub ( Real.continuous_cos.measurable.comp ( measurable_const.mul measurable_id' ) ) ) ( measurable_id'.pow_const _ |> Measurable.inv ) );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with s hs using h_bound s hs;
  convert h_split.1.union h_split.2 using 1 ; norm_num

/-
The basic kernel `g q` is integrable on `(0, ∞)` (the `t = 1` case).
-/
lemma integrable_g {q : ℝ} (hq0 : 0 < q) (hq2 : q < 2) :
    IntegrableOn (g q) (Ioi 0) := by
  convert integrable_kern hq0 hq2 1 using 1 ; ext ; unfold g ; norm_num

/-
Scaling: `∫_{(0,∞)} (1 - cos (t s))/s^{1+q} ds = |t|^q * K`.
-/
lemma integral_kern_eq {q : ℝ} (hq0 : 0 < q) (t : ℝ) :
    (∫ s in Ioi (0 : ℝ), (1 - Real.cos (t * s)) / s ^ (1 + q)) = |t| ^ q * Kconst q := by
  by_cases ht : t = 0;
  · simp +decide [ ht, hq0.ne' ];
  · -- By substitution using $ u = |t| s $, we can transform the integral.
    have h_subst : ∫ (s : ℝ) in Ioi 0, (1 - Real.cos (|t| * s)) / s ^ (1 + q) = |t| ^ q * ∫ (u : ℝ) in Ioi 0, (1 - Real.cos u) / u ^ (1 + q) := by
      have h_subst : ∀ {f : ℝ → ℝ}, (∫ (s : ℝ) in Ioi 0, f s) = (∫ (u : ℝ) in Ioi 0, f (u / |t|) / |t|) := by
        intro f; rw [ MeasureTheory.integral_div ] ; simp +decide [ div_eq_inv_mul ] ;
        rw [ MeasureTheory.integral_comp_mul_left_Ioi ] <;> norm_num [ ht ];
      convert @h_subst ( fun s => ( 1 - Real.cos ( |t| * s ) ) / s ^ ( 1 + q ) ) using 1;
      rw [ ← MeasureTheory.integral_const_mul ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => _ ; rw [ mul_div_cancel₀ _ ( ne_of_gt ( abs_pos.mpr ht ) ) ] ; rw [ Real.div_rpow ( le_of_lt hu ) ( by positivity ) ] ; ring_nf;
      norm_num [ Real.rpow_add ( abs_pos.mpr ht ), Real.rpow_one ] ; ring_nf;
      norm_num [ ht ];
    unfold Kconst g
    convert h_subst using 3;
    cases abs_cases t <;> simp +decide [ * ]

/-
The normalising constant is strictly positive.
-/
lemma Kconst_pos {q : ℝ} (hq0 : 0 < q) (hq2 : q < 2) : 0 < Kconst q := by
  refine' ( lt_of_le_of_ne _ _ );
  · exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun x hx => div_nonneg ( sub_nonneg.2 ( Real.cos_le_one x ) ) ( Real.rpow_nonneg hx.out.le _ );
  · refine' ne_of_lt _;
    -- We need to show that the integral of $(1 - \cos u) / u^{1 + q}$ over $(0, \infty)$ is positive.
    have h_integral_pos : 0 < ∫ u in Set.Ioo 0 1, (1 - Real.cos u) / u ^ (1 + q) := by
      rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
      · simp +decide [ Function.support ];
        exact ( lt_of_lt_of_le ( by norm_num ) ( MeasureTheory.measure_mono ( show Set.Ioo 0 1 ⊆ { x : ℝ | ¬1 - Real.cos x = 0 ∧ ¬x ^ ( 1 + q ) = 0 } ∩ Ioo 0 1 from fun x hx => ⟨ ⟨ by exact ne_of_gt ( by nlinarith [ Real.sin_sq_add_cos_sq x, Real.sin_pos_of_pos_of_lt_pi hx.1 ( by linarith [ Real.pi_gt_three, hx.2 ] ) ] ), by exact ne_of_gt ( Real.rpow_pos_of_pos hx.1 _ ) ⟩, hx ⟩ ) ) );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with u hu using div_nonneg ( sub_nonneg.2 ( Real.cos_le_one u ) ) ( Real.rpow_nonneg hu.1.le _ );
      · refine' MeasureTheory.IntegrableOn.mono_set _ ( Set.Ioo_subset_Ioi_self );
        convert integrable_g hq0 hq2 using 1
        ext u
        rfl
    refine' h_integral_pos.trans_le ( MeasureTheory.setIntegral_mono_set _ _ _ );
    · convert integrable_g hq0 hq2 using 1
      ext u
      rfl
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using div_nonneg ( sub_nonneg.2 ( Real.cos_le_one u ) ) ( Real.rpow_nonneg hu.out.le _ );
    · exact MeasureTheory.ae_of_all _ fun x hx => hx.1

/-
Pointwise nonpositivity of the kernel sum: for weights summing to zero,
`∑ₓ ∑ᵧ c x * c y * (1 - cos ((x - y) s)) ≤ 0`.
-/
lemma pointwise_nonpos (S : Finset ℝ) (c : ℝ → ℝ) (hc : ∑ x ∈ S, c x = 0) (s : ℝ) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * (1 - Real.cos ((x - y) * s)) ≤ 0 := by
  -- Since $\sum_{x \in S} c_x = 0$, the constant part vanishes.
  have h_const : ∑ x ∈ S, ∑ y ∈ S, c x * c y * (1 - Real.cos ((x - y) * s)) = - (∑ x ∈ S, c x * Real.cos (x * s))^2 - (∑ x ∈ S, c x * Real.sin (x * s))^2 := by
    simp +decide [ Real.cos_sub, mul_sub, pow_two, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
    simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, hc ] ; ring;
  nlinarith

/-
Negative type for `0 < q < 2`, via the integral representation.
-/
lemma neg_type_lt_two {q : ℝ} (hq0 : 0 < q) (hq2 : q < 2)
    (S : Finset ℝ) (c : ℝ → ℝ) (hc : ∑ x ∈ S, c x = 0) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * |x - y| ^ q ≤ 0 := by
  have h_integral : ∫ s in Set.Ioi (0 : ℝ), ∑ x ∈ S, ∑ y ∈ S, c x * c y * (1 - Real.cos ((x - y) * s)) / s ^ (1 + q) ≤ 0 := by
    refine' MeasureTheory.setIntegral_nonpos measurableSet_Ioi fun s hs => _;
    simpa only [ ← Finset.sum_div, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] using div_nonpos_of_nonpos_of_nonneg ( pointwise_nonpos S c hc s ) ( Real.rpow_nonneg hs.out.le _ );
  -- By Fubini's theorem, we can interchange the order of summation and integration.
  have h_fubini : ∫ s in Set.Ioi (0 : ℝ), ∑ x ∈ S, ∑ y ∈ S, c x * c y * (1 - Real.cos ((x - y) * s)) / s ^ (1 + q) = ∑ x ∈ S, ∑ y ∈ S, c x * c y * ∫ s in Set.Ioi (0 : ℝ), (1 - Real.cos ((x - y) * s)) / s ^ (1 + q) := by
    have h_fubini : ∀ x ∈ S, ∀ y ∈ S, MeasureTheory.IntegrableOn (fun s => c x * c y * (1 - Real.cos ((x - y) * s)) / s ^ (1 + q)) (Set.Ioi (0 : ℝ)) := by
      intro x hx y hy; specialize h_integral; have := integrable_kern hq0 hq2 ( x - y ) ; simp_all +decide [ mul_div_assoc ] ;
      exact this.const_mul _;
    rw [ MeasureTheory.integral_finsetSum ];
    · exact Finset.sum_congr rfl fun x hx => by rw [ MeasureTheory.integral_finsetSum _ fun y hy => h_fubini x hx y hy ] ; exact Finset.sum_congr rfl fun y hy => by simp +decide only [mul_div_assoc, integral_const_mul] ;
    · exact fun x hx => MeasureTheory.integrable_finsetSum _ fun y hy => h_fubini x hx y hy;
  have hK_nonneg : 0 ≤ Kconst q := le_of_lt (Kconst_pos hq0 hq2)
  have hsum_eq : ∑ x ∈ S, ∑ y ∈ S, c x * c y * |x - y| ^ q =
      (∫ s in Set.Ioi (0 : ℝ), ∑ x ∈ S, ∑ y ∈ S,
        c x * c y * (1 - Real.cos ((x - y) * s)) / s ^ (1 + q)) / Kconst q := by
    rw [ h_fubini, eq_div_iff ];
    · simp +decide only [mul_assoc, Finset.sum_mul];
      exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [ integral_kern_eq hq0 ( x - y ) ] ;
    · exact ne_of_gt ( Kconst_pos hq0 hq2 );
  rw [hsum_eq]
  exact div_nonpos_of_nonpos_of_nonneg h_integral hK_nonneg

/-
Negative type for the endpoint `q = 2`, algebraically.
-/
lemma neg_type_two
    (S : Finset ℝ) (c : ℝ → ℝ) (hc : ∑ x ∈ S, c x = 0) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * |x - y| ^ (2 : ℝ) ≤ 0 := by
  -- Expand $(x-y)^2 = x^2 - 2xy + y^2$.
  have h_expand : ∑ x ∈ S, ∑ y ∈ S, (c x) * (c y) * (x - y) ^ 2 = (∑ x ∈ S, c x * x ^ 2) * (∑ y ∈ S, c y) - 2 * (∑ x ∈ S, c x * x) * (∑ y ∈ S, c y * y) + (∑ x ∈ S, c x) * (∑ y ∈ S, c y * y ^ 2) := by
    simp +decide [ sub_sq, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm ] ;
    simpa only [ ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by ring;
  simp_all +decide ; nlinarith [ sq_nonneg ( ∑ x ∈ S, c x * x ) ] ;

/-- **Every finite subset of `ℝ` has `q`-negative type for `0 < q ≤ 2`.**
For a finite set `S ⊆ ℝ` and weights `c : ℝ → ℝ` summing to zero on `S`,
`∑ₓ∈S ∑ᵧ∈S c x * c y * |x - y|^q ≤ 0`. -/
theorem real_finite_negative_type {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2)
    (S : Finset ℝ) (c : ℝ → ℝ) (hc : ∑ x ∈ S, c x = 0) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * |x - y| ^ q ≤ 0 := by
  rcases lt_or_eq_of_le hq2 with h | h
  · exact neg_type_lt_two hq0 h S c hc
  · subst h; exact neg_type_two S c hc

end NegType

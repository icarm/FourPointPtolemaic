import Mathlib

open scoped BigOperators
open MeasureTheory

namespace ExpKernel

/-!
# Conditionally-negative-type kernels and downward closure

This file develops, abstractly over a finite index type, the positivity machinery
needed for Blumenthal's theorem (the case `0 < q ≤ 1`):

* `QPos B` : the symmetric kernel `B` has nonnegative quadratic form.
* Schur product theorem (`QPos.mul`), Schur powers (`QPos.pow`), and the
  exponential kernel (`QPos.exp`).
* The Gaussian / "negative-distance" kernel `exp (-(t * d))` is `QPos`
  (`qpos_exp_neg_dist`), and hence the resolvent kernel `1 / (t + d)` is `QPos`
  (`qpos_resolvent`).
* Downward closure: if `d` is a conditionally-negative-type kernel realized as
  `d i j = B i i + B j j - 2 B i j` with `QPos B`, then `d ^ p` is again of
  negative type for `0 < p < 1` (`qpos_downward`).
-/

variable {ι : Type*} [Fintype ι]

/-- A symmetric real kernel has nonnegative quadratic form. -/
def QPos (B : ι → ι → ℝ) : Prop :=
  ∀ a : ι → ℝ, 0 ≤ ∑ i, ∑ j, a i * a j * B i j

lemma QPos.smul {B : ι → ι → ℝ} (hB : QPos B) {c : ℝ} (hc : 0 ≤ c) :
    QPos (fun i j => c * B i j) := by
  intro a
  simpa +decide only [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _,
    Finset.sum_mul] using mul_nonneg hc (hB a)

/-
The constant kernel `1` is `QPos` (its quadratic form is `(∑ a)^2`).
-/
lemma qpos_one : QPos (fun _ _ : ι => (1 : ℝ)) := by
  intro a
  simp;
  simpa only [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] using mul_self_nonneg _

/-
Bridge to `Matrix.PosSemidef`: a symmetric `QPos` kernel is positive semidefinite
as a matrix.
-/
lemma posSemidef_of_qpos {B : ι → ι → ℝ} (hsymm : ∀ i j, B i j = B j i)
    (hB : QPos B) : (Matrix.of (fun i j => B i j)).PosSemidef := by
  constructor;
  · ext i j; simp +decide [ hsymm ] ;
  · intro x
    simpa +decide [Finsupp.sum_fintype, mul_comm, mul_left_comm] using hB (fun i => x i)

open Matrix in
open scoped MatrixOrder in
/-- A matrix is positive semidefinite iff it has the form `Bᴴ * B`. Non-deprecated
restatement of the former `Matrix.posSemidef_iff_eq_conjTranspose_mul_self`. -/
private lemma posSemidef_iff_eq_conjTranspose_mul_self [DecidableEq ι] {A : Matrix ι ι ℝ} :
    A.PosSemidef ↔ ∃ B : Matrix ι ι ℝ, A = Bᴴ * B :=
  Matrix.nonneg_iff_posSemidef.symm.trans CStarAlgebra.nonneg_iff_eq_star_mul_self

/-
**Schur product theorem.** The entrywise product of two `QPos` kernels is `QPos`.
-/
lemma QPos.mul [DecidableEq ι] {B C : ι → ι → ℝ}
    (_hBsymm : ∀ i j, B i j = B j i) (hB : QPos B)
    (hCsymm : ∀ i j, C i j = C j i) (hC : QPos C) :
    QPos (fun i j => B i j * C i j) := by
  obtain ⟨ D, hD ⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp ( posSemidef_of_qpos hCsymm hC );
  -- Substitute C i j = ∑ k, D k i * D k j into the quadratic form.
  intro a
  simp [hD] at *;
  have hD : ∃ D : Matrix ι ι ℝ, ∀ i j, C i j = ∑ k, D k i * D k j := by
    have := posSemidef_iff_eq_conjTranspose_mul_self.mp ( posSemidef_of_qpos hCsymm hC );
    obtain ⟨ D, hD ⟩ := this; use D; intro i j; simpa [ Matrix.mul_apply, mul_comm ] using congr_fun ( congr_fun hD i ) j;
  obtain ⟨ D, hD ⟩ := hD; simp +decide only [hD] ; ring_nf; (
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ x, ∑ x_1, a x * a x_1 * B x x_1 * ∑ x_2, D x_2 x * D x_2 x_1 = ∑ x_2, ∑ x, ∑ x_1, a x * a x_1 * B x x_1 * D x_2 x * D x_2 x_1 := by
    simp +decide only [mul_assoc, Finset.mul_sum _ _ _] ; exact Eq.symm ( Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm ) ) ;
  exact h_fubini.symm ▸ Finset.sum_nonneg fun k _ => by simpa [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] using hB ( fun i => a i * D k i ) ;);

/-
**Schur powers.** Every entrywise power of a `QPos` symmetric kernel is `QPos`.
-/
lemma QPos.pow [DecidableEq ι] {B : ι → ι → ℝ} (hsymm : ∀ i j, B i j = B j i)
    (hB : QPos B) : ∀ n : ℕ, QPos (fun i j => (B i j) ^ n) := by
  intro n;
  induction' n with n ih;
  · simpa using qpos_one;
  · convert QPos.mul hsymm hB ( fun i j => hsymm i j ▸ by ring ) ih using 1 ; ext i j ; ring

/-
**The exponential kernel** of a `QPos` symmetric kernel is `QPos`.
-/
lemma QPos.exp [DecidableEq ι] {B : ι → ι → ℝ} (hsymm : ∀ i j, B i j = B j i)
    (hB : QPos B) : QPos (fun i j => Real.exp (B i j)) := by
  intro a;
  -- For each i,j, a i * a j * Real.exp (B i j) = ∑' n, a i * a j * (B i j)^n / n!, and this series is summable (constant multiple of the exp series).
  have h_series : ∀ i j, a i * a j * Real.exp (B i j) = ∑' n : ℕ, (a i * a j * (B i j)^n) / (Nat.factorial n) := by
    simp +decide [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div, mul_div_assoc, tsum_mul_left ];
  -- Interchange the finite double sum with the tsum:
  have h_interchange : ∑ i, ∑ j, ∑' n : ℕ, (a i * a j * (B i j)^n) / (Nat.factorial n) = ∑' n : ℕ, ∑ i, ∑ j, (a i * a j * (B i j)^n) / (Nat.factorial n) := by
    have h_fubini : ∀ {f : ℕ → ι → ι → ℝ}, (∀ i j, Summable (fun n => f n i j)) → ∑ i, ∑ j, ∑' n, f n i j = ∑' n, ∑ i, ∑ j, f n i j := by
      intro f hf;
      have h_fubini : ∀ {f : ℕ → ι → ℝ}, (∀ i, Summable (fun n => f n i)) → ∑ i, ∑' n, f n i = ∑' n, ∑ i, f n i := by
        exact fun {f} a => Eq.symm (Summable.tsum_finsetSum fun i a_1 => a i);
      rw [ Finset.sum_congr rfl fun i _ => h_fubini fun j => hf i j, h_fubini fun i => by exact summable_sum fun j _ => hf i j ];
    apply h_fubini;
    exact fun i j => by simpa only [ mul_div_assoc ] using Summable.mul_left _ ( Real.summable_pow_div_factorial _ ) ;
  simp_all +decide [ div_eq_mul_inv, ← Finset.sum_mul ];
  exact tsum_nonneg fun n => mul_nonneg ( by simpa only [ mul_assoc, mul_comm, mul_left_comm ] using QPos.pow hsymm hB n a ) ( by positivity )

/-
**The negative-distance (Gaussian) kernel.** If `d i j = B i i + B j j - 2 B i j`
with `B` symmetric and `QPos`, then for every `t ≥ 0` the kernel
`exp (-(t * d i j))` is `QPos`.
-/
lemma qpos_exp_neg_dist [DecidableEq ι] {B d : ι → ι → ℝ}
    (hsymm : ∀ i j, B i j = B j i) (hB : QPos B)
    (hrel : ∀ i j, d i j = B i i + B j j - 2 * B i j) {t : ℝ} (ht : 0 ≤ t) :
    QPos (fun i j => Real.exp (-(t * d i j))) := by
  -- Define `a' i := a i * Real.exp (-(t * B i i))`.
  intro a
  have h_exp : ∀ i j, Real.exp (-(t * d i j)) = Real.exp (-(t * B i i)) * Real.exp (-(t * B j j)) * Real.exp ((2 * t) * B i j) := by
    intro i j; rw [ hrel i j ] ; rw [ ← Real.exp_add, ← Real.exp_add ] ; ring_nf;
  have h_exp_smul : QPos (fun i j => Real.exp ((2 * t) * B i j)) := by
    convert QPos.exp ( show ∀ i j, ( 2 * t * B i j ) = ( 2 * t * B j i ) by simp +decide [ hsymm ] ) ( QPos.smul hB ( show 0 ≤ 2 * t by positivity ) ) using 1;
  convert h_exp_smul ( fun i => a i * Real.exp ( - ( t * B i i ) ) ) using 1 ; simp +decide [ h_exp, mul_assoc, mul_comm, mul_left_comm ]

/-
**The resolvent kernel.** Under the same hypotheses, for `t > 0` the kernel
`1 / (t + d i j)` is `QPos`.
-/
lemma qpos_resolvent [DecidableEq ι] {B d : ι → ι → ℝ}
    (hsymm : ∀ i j, B i j = B j i) (hB : QPos B)
    (hrel : ∀ i j, d i j = B i i + B j j - 2 * B i j)
    (hdnn : ∀ i j, 0 ≤ d i j) {t : ℝ} (ht : 0 < t) (a : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, a i * a j * (1 / (t + d i j)) := by
  -- By Fubini's theorem, we can interchange the order of summation and integration.
  have h_fubini : ∑ i, ∑ j, a i * a j * (∫ s in Set.Ioi 0, Real.exp (-(t + d i j) * s)) = ∫ s in Set.Ioi 0, ∑ i, ∑ j, a i * a j * Real.exp (-(t + d i j) * s) := by
    rw [ MeasureTheory.integral_finsetSum ];
    · refine' Finset.sum_congr rfl fun i _ => _;
      rw [ MeasureTheory.integral_finsetSum ];
      · simp +decide only [integral_const_mul];
      · intro j _
        have hint : IntegrableOn (fun s => Real.exp (-(t + d i j) * s)) (Set.Ioi 0) := by
          simpa [mul_comm] using
            (exp_neg_integrableOn_Ioi 0 (show 0 < t + d i j by linarith [hdnn i j]))
        exact hint.integrable.const_mul _
    · intro i hi; refine' MeasureTheory.integrable_finsetSum _ _; intro j hj; refine' MeasureTheory.Integrable.const_mul _ _;
      have hint : IntegrableOn (fun s => Real.exp (-(t + d i j) * s)) (Set.Ioi 0) := by
        simpa [mul_comm] using
          (exp_neg_integrableOn_Ioi 0 (show 0 < t + d i j by linarith [hdnn i j]))
      exact (hint.mono_set <| Set.Ioi_subset_Ioi <| by linarith).integrable
  -- Now use the fact that the inner sum is non-negative by qpos_exp_neg_dist.
  have h_inner_nonneg : ∀ s ∈ Set.Ioi 0, 0 ≤ ∑ i, ∑ j, a i * a j * Real.exp (-(t + d i j) * s) := by
    intro s hs
    have h_inner : 0 ≤ ∑ i, ∑ j, a i * a j * Real.exp (-(s * d i j)) := by
      convert qpos_exp_neg_dist hsymm hB hrel hs.out.le a using 1;
    have hscale :
        ∑ i, ∑ j, a i * a j * Real.exp (-(t + d i j) * s)
          = Real.exp (-(t * s)) * ∑ i, ∑ j, a i * a j * Real.exp (-(s * d i j)) := by
      simp +decide only [Finset.mul_sum _ _ _, mul_assoc, mul_comm,
        mul_left_comm]
      exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by
        rw [← Real.exp_add]
        ring_nf
    rw [hscale]
    exact mul_nonneg (Real.exp_nonneg (-(t * s))) h_inner
  convert h_fubini.symm ▸ MeasureTheory.setIntegral_nonneg measurableSet_Ioi h_inner_nonneg using 1;
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [ show ∫ s in Set.Ioi 0, Real.exp ( - ( t + d i j ) * s ) = 1 / ( t + d i j ) by have := integral_exp_neg_mul_rpow zero_lt_one ( show 0 < t + d i j by linarith [ hdnn i j ] ) ; norm_num [ Real.rpow_neg_one ] at this ⊢; linarith ] ;

/-
**Downward closure.** If `d i j = B i i + B j j - 2 B i j` with `B` a symmetric
`QPos` kernel (so `d` is a conditionally-negative-type kernel) and `0 < p < 1`,
then `d ^ p` is again of negative type: its quadratic form is `≤ 0` on every
weight vector summing to zero.
-/
theorem qpos_downward [DecidableEq ι] {B d : ι → ι → ℝ}
    (hsymm : ∀ i j, B i j = B j i) (hB : QPos B)
    (hrel : ∀ i j, d i j = B i i + B j j - 2 * B i j)
    (hdnn : ∀ i j, 0 ≤ d i j) {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (a : ι → ℝ) (ha : ∑ i, a i = 0) :
    ∑ i, ∑ j, a i * a j * (d i j) ^ p ≤ 0 := by
  -- By Real.rpow_eq_const_mul_integral , for every i,j:
  have hrpow : ∀ i j, (d i j) ^ p = (∫ t in Set.Ioi 0, (Real.rpowIntegrand₀₁ p t (d i j))) / (∫ t in Set.Ioi 0, (Real.rpowIntegrand₀₁ p t 1)) := by
    intro i j; rw [ Real.rpow_eq_const_mul_integral hp ( hdnn i j ) ] ; ring;
  -- So
  have hsum : ∑ i, ∑ j, a i * a j * (d i j) ^ p = (∫ t in Set.Ioi 0, (∑ i, ∑ j, a i * a j * (Real.rpowIntegrand₀₁ p t (d i j)))) / (∫ t in Set.Ioi 0, (Real.rpowIntegrand₀₁ p t 1)) := by
    rw [ MeasureTheory.integral_finsetSum, Finset.sum_div ];
    · refine' Finset.sum_congr rfl fun i _ => _;
      rw [ MeasureTheory.integral_finsetSum ];
      · simp +decide only [hrpow, mul_assoc, integral_const_mul, Finset.sum_div];
        exact Finset.sum_congr rfl fun _ _ => by ring;
      · intro j _;
        refine' MeasureTheory.Integrable.const_mul _ _;
        apply_rules [ Real.integrableOn_rpowIntegrand₀₁_Ioi ];
    · intro i _; apply_rules [ MeasureTheory.integrable_finsetSum, MeasureTheory.Integrable.const_mul ] ;
      intro j _;
      exact MeasureTheory.Integrable.const_mul ( Real.integrableOn_rpowIntegrand₀₁_Ioi hp ( hdnn i j ) ) _;
  -- For t > 0:
  have h_integrand_nonpos : ∀ t > 0, ∑ i, ∑ j, a i * a j * (Real.rpowIntegrand₀₁ p t (d i j)) ≤ 0 := by
    intro t ht
    have h_integrand_nonpos_step : ∑ i, ∑ j, a i * a j * (Real.rpowIntegrand₀₁ p t (d i j)) = t^(p-1) * (∑ i, ∑ j, a i * a j * (1 - t * (1 / (t + d i j)))) := by
      have h_integrand_nonpos_step : ∀ i j, (Real.rpowIntegrand₀₁ p t (d i j)) = t^(p-1) * (1 - t * (1 / (t + d i j))) := by
        intro i j
        have h_integrand_nonpos_step : (Real.rpowIntegrand₀₁ p t (d i j)) = t^(p-1) * (d i j / (t + d i j)) := by
          convert Real.rpowIntegrand₀₁_eq_pow_div hp ht.le ( hdnn i j ) using 1;
          ring;
        grind;
      simp +decide only [h_integrand_nonpos_step, Finset.mul_sum _ _ _, mul_left_comm];
    -- Using the fact that $\sum_{i} a_i = 0$, we can simplify the expression.
    have h_simplify : ∑ i, ∑ j, a i * a j * (1 - t * (1 / (t + d i j))) = -t * ∑ i, ∑ j, a i * a j * (1 / (t + d i j)) := by
      simp +decide [ mul_sub, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm ];
      simp +decide [ ← Finset.mul_sum _ _ _, ha ];
    exact h_integrand_nonpos_step.symm ▸ mul_nonpos_of_nonneg_of_nonpos ( Real.rpow_nonneg ht.le _ ) ( h_simplify.symm ▸ mul_nonpos_of_nonpos_of_nonneg ( neg_nonpos.mpr ht.le ) ( qpos_resolvent hsymm hB hrel hdnn ht a ) );
  refine' hsum ▸ div_nonpos_of_nonpos_of_nonneg ( MeasureTheory.setIntegral_nonpos measurableSet_Ioi fun t ht => h_integrand_nonpos t ht ) ( MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun t ht => _ );
  refine' mul_nonneg _ _ <;> norm_num;
  · exact Real.rpow_nonneg ht.out.le _;
  · exact inv_anti₀ ht ( by linarith )

end ExpKernel

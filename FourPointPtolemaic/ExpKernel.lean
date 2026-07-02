import Mathlib

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

open MeasureTheory

namespace ExpKernel

variable {ι : Type*} [Fintype ι]

/-- A symmetric real kernel has nonnegative quadratic form. -/
def QPos (B : ι → ι → ℝ) : Prop :=
  ∀ a : ι → ℝ, 0 ≤ ∑ i, ∑ j, a i * a j * B i j

lemma QPos.smul {B : ι → ι → ℝ} (hB : QPos B) {c : ℝ} (hc : 0 ≤ c) :
    QPos fun i j => c * B i j := by
  intro a
  simpa only [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
    using mul_nonneg hc (hB a)

/-- The constant kernel `1` is `QPos`: its quadratic form is `(∑ i, a i) ^ 2`. -/
lemma qpos_one : QPos fun _ _ : ι => (1 : ℝ) := fun a => by
  simpa only [mul_one, ← Finset.mul_sum, ← Finset.sum_mul] using mul_self_nonneg (∑ i, a i)

/-- A symmetric `QPos` kernel is positive semidefinite as a matrix. -/
lemma posSemidef_of_qpos {B : ι → ι → ℝ} (hsymm : ∀ i j, B i j = B j i)
    (hB : QPos B) : (Matrix.of B).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp [hsymm i j]
  · simpa [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
      using hB x

/-- A positive semidefinite matrix is `QPos` as a kernel. -/
lemma qpos_of_posSemidef {B : ι → ι → ℝ} (hB : (Matrix.of B).PosSemidef) : QPos B := fun a => by
  simpa [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
    using hB.dotProduct_mulVec_nonneg a

/-- **Schur product theorem.** The entrywise product of two `QPos` kernels is `QPos`. -/
lemma QPos.mul {B C : ι → ι → ℝ}
    (hBsymm : ∀ i j, B i j = B j i) (hB : QPos B)
    (hCsymm : ∀ i j, C i j = C j i) (hC : QPos C) :
    QPos fun i j => B i j * C i j :=
  qpos_of_posSemidef ((posSemidef_of_qpos hBsymm hB).hadamard (posSemidef_of_qpos hCsymm hC))

/-- **Schur powers.** Every entrywise power of a `QPos` symmetric kernel is `QPos`. -/
lemma QPos.pow {B : ι → ι → ℝ} (hsymm : ∀ i j, B i j = B j i)
    (hB : QPos B) : ∀ n : ℕ, QPos fun i j => B i j ^ n := by
  intro n
  induction n with
  | zero => simpa using qpos_one
  | succ n ih =>
    simpa only [pow_succ] using
      QPos.mul (fun i j => by rw [hsymm]) ih hsymm hB

/-- The entrywise exponential of a `QPos` symmetric kernel is `QPos`. -/
lemma QPos.exp {B : ι → ι → ℝ} (hsymm : ∀ i j, B i j = B j i)
    (hB : QPos B) : QPos fun i j => Real.exp (B i j) := by
  intro a
  have hsummable : ∀ i j : ι, Summable fun n : ℕ => a i * a j * B i j ^ n / n.factorial :=
    fun i j => by
      simpa only [mul_div_assoc]
        using (Real.summable_pow_div_factorial (B i j)).mul_left (a i * a j)
  have hseries : ∀ i j, a i * a j * Real.exp (B i j)
      = ∑' n : ℕ, a i * a j * B i j ^ n / n.factorial := by
    intro i j
    simp [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div, mul_div_assoc, tsum_mul_left]
  calc (0 : ℝ)
      ≤ ∑' n : ℕ, ∑ i, ∑ j, a i * a j * B i j ^ n / n.factorial := by
        refine tsum_nonneg fun n => ?_
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        exact mul_nonneg (QPos.pow hsymm hB n a) (by positivity)
    _ = ∑ i, ∑ j, ∑' n : ℕ, a i * a j * B i j ^ n / n.factorial := by
        rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hsummable i j]
        exact Finset.sum_congr rfl fun i _ => Summable.tsum_finsetSum fun j _ => hsummable i j
    _ = ∑ i, ∑ j, a i * a j * Real.exp (B i j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (hseries i j).symm

/-- **The negative-distance (Gaussian) kernel.** If `d i j = B i i + B j j - 2 B i j`
with `B` symmetric and `QPos`, then for every `t ≥ 0` the kernel
`exp (-(t * d i j))` is `QPos`. -/
lemma qpos_exp_neg_dist {B d : ι → ι → ℝ}
    (hsymm : ∀ i j, B i j = B j i) (hB : QPos B)
    (hrel : ∀ i j, d i j = B i i + B j j - 2 * B i j) {t : ℝ} (ht : 0 ≤ t) :
    QPos fun i j => Real.exp (-(t * d i j)) := by
  intro a
  have hfactor : ∀ i j, Real.exp (-(t * d i j))
      = Real.exp (-(t * B i i)) * Real.exp (-(t * B j j)) * Real.exp (2 * t * B i j) := by
    intro i j
    rw [hrel, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hqpos : QPos fun i j => Real.exp (2 * t * B i j) :=
    QPos.exp (show ∀ i j, 2 * t * B i j = 2 * t * B j i from fun i j => by rw [hsymm])
      (hB.smul (by positivity))
  simpa only [hfactor, mul_assoc, mul_comm, mul_left_comm]
    using hqpos fun i => a i * Real.exp (-(t * B i i))

/-- Interchange a double finite sum with an integral over `Set.Ioi 0`. -/
private lemma sum_sum_integral_comm {f : ι → ι → ℝ → ℝ}
    (hf : ∀ i j, IntegrableOn (f i j) (Set.Ioi 0)) :
    ∑ i, ∑ j, ∫ s in Set.Ioi 0, f i j s = ∫ s in Set.Ioi 0, ∑ i, ∑ j, f i j s := by
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hf i j]
  exact Finset.sum_congr rfl fun i _ => (integral_finsetSum _ fun j _ => hf i j).symm

/-- **The resolvent kernel.** Under the same hypotheses, for `t > 0` the kernel
`1 / (t + d i j)` is `QPos`. -/
lemma qpos_resolvent {B d : ι → ι → ℝ}
    (hsymm : ∀ i j, B i j = B j i) (hB : QPos B)
    (hrel : ∀ i j, d i j = B i i + B j j - 2 * B i j)
    (hdnn : ∀ i j, 0 ≤ d i j) {t : ℝ} (ht : 0 < t) (a : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, a i * a j * (1 / (t + d i j)) := by
  have htd : ∀ i j, 0 < t + d i j := fun i j => by linarith [hdnn i j]
  have hint : ∀ i j, IntegrableOn (fun s => a i * a j * Real.exp (-(t + d i j) * s))
      (Set.Ioi 0) :=
    fun i j => ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (htd i j)) 0).integrable.const_mul _)
  have hval : ∀ i j, ∫ s in Set.Ioi 0, Real.exp (-(t + d i j) * s) = 1 / (t + d i j) := by
    intro i j
    rw [integral_exp_mul_Ioi (neg_lt_zero.mpr (htd i j)), mul_zero, Real.exp_zero, neg_div_neg_eq]
  calc (0 : ℝ)
      ≤ ∫ s in Set.Ioi 0, ∑ i, ∑ j, a i * a j * Real.exp (-(t + d i j) * s) := by
        refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
        have hsplit : ∀ i j, a i * a j * Real.exp (-(t + d i j) * s)
            = Real.exp (-(t * s)) * (a i * a j * Real.exp (-(s * d i j))) := by
          intro i j
          rw [mul_left_comm, ← Real.exp_add]
          ring_nf
        calc (0 : ℝ)
            ≤ Real.exp (-(t * s)) * ∑ i, ∑ j, a i * a j * Real.exp (-(s * d i j)) :=
              mul_nonneg (Real.exp_nonneg _) (qpos_exp_neg_dist hsymm hB hrel hs.out.le a)
          _ = ∑ i, ∑ j, a i * a j * Real.exp (-(t + d i j) * s) := by
              simp only [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
                (hsplit i j).symm
    _ = ∑ i, ∑ j, ∫ s in Set.Ioi 0, a i * a j * Real.exp (-(t + d i j) * s) :=
        (sum_sum_integral_comm hint).symm
    _ = ∑ i, ∑ j, a i * a j * (1 / (t + d i j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [integral_const_mul, hval]

/-- **Downward closure.** If `d i j = B i i + B j j - 2 B i j` with `B` a symmetric
`QPos` kernel (so `d` is a conditionally-negative-type kernel) and `0 < p < 1`,
then `d ^ p` is again of negative type: its quadratic form is `≤ 0` on every
weight vector summing to zero. -/
theorem qpos_downward {B d : ι → ι → ℝ}
    (hsymm : ∀ i j, B i j = B j i) (hB : QPos B)
    (hrel : ∀ i j, d i j = B i i + B j j - 2 * B i j)
    (hdnn : ∀ i j, 0 ≤ d i j) {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (a : ι → ℝ) (ha : ∑ i, a i = 0) :
    ∑ i, ∑ j, a i * a j * d i j ^ p ≤ 0 := by
  -- Represent `d i j ^ p` as a normalized integral of resolvent kernels.
  have hrpow : ∀ i j, d i j ^ p
      = (∫ t in Set.Ioi 0, Real.rpowIntegrand₀₁ p t 1)⁻¹
        * ∫ t in Set.Ioi 0, Real.rpowIntegrand₀₁ p t (d i j) :=
    fun i j => Real.rpow_eq_const_mul_integral hp (hdnn i j)
  have hint : ∀ i j, IntegrableOn (fun t => a i * a j * Real.rpowIntegrand₀₁ p t (d i j))
      (Set.Ioi 0) :=
    fun i j => (Real.integrableOn_rpowIntegrand₀₁_Ioi hp (hdnn i j)).integrable.const_mul _
  have hsum : ∑ i, ∑ j, a i * a j * d i j ^ p
      = (∫ t in Set.Ioi 0, Real.rpowIntegrand₀₁ p t 1)⁻¹
        * ∫ t in Set.Ioi 0, ∑ i, ∑ j, a i * a j * Real.rpowIntegrand₀₁ p t (d i j) := by
    rw [← sum_sum_integral_comm hint]
    simp only [hrpow, integral_const_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h0 : ∑ i, ∑ j, a i * a j = 0 := by
    simp only [← Finset.sum_mul_sum, ha, zero_mul]
  -- For `t > 0`, `rpowIntegrand₀₁ p t x = t ^ p * (t⁻¹ - (t + x)⁻¹)` by definition; since the
  -- weights sum to zero, only the resolvent part survives, and `qpos_resolvent` gives its sign.
  have h_nonpos : ∀ t ∈ Set.Ioi (0 : ℝ),
      ∑ i, ∑ j, a i * a j * Real.rpowIntegrand₀₁ p t (d i j) ≤ 0 := by
    intro t ht
    replace ht : 0 < t := ht
    calc ∑ i, ∑ j, a i * a j * Real.rpowIntegrand₀₁ p t (d i j)
        = t ^ p * t⁻¹ * (∑ i, ∑ j, a i * a j)
            - t ^ p * ∑ i, ∑ j, a i * a j * (1 / (t + d i j)) := by
          simp only [Real.rpowIntegrand₀₁, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = -(t ^ p * ∑ i, ∑ j, a i * a j * (1 / (t + d i j))) := by
          rw [h0, mul_zero, zero_sub]
      _ ≤ 0 := neg_nonpos.mpr (mul_nonneg (Real.rpow_nonneg ht.le _)
          (qpos_resolvent hsymm hB hrel hdnn ht a))
  rw [hsum]
  exact mul_nonpos_of_nonneg_of_nonpos
    (inv_nonneg.mpr (setIntegral_nonneg measurableSet_Ioi fun t ht =>
      Real.rpowIntegrand₀₁_nonneg hp.1 ht.out.le zero_le_one))
    (setIntegral_nonpos measurableSet_Ioi h_nonpos)

end ExpKernel

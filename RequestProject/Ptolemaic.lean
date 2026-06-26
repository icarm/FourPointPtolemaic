import Mathlib
import RequestProject.Main
import RequestProject.ExpKernel

open scoped BigOperators
open scoped Real

namespace Ptolemaic

/-!
# Four-point Ptolemaic metrics have `q`-negative type for `0 < q ≤ log₂ 3`

This file formalizes the "Four-point Ptolemaic snowflake theorem":
every four-point Ptolemaic metric space has `q`-negative type for `0 < q ≤ log₂ 3`.
-/

/-- A (pseudo)metric on the four-point set `Fin 4`. -/
def IsMetric4 (d : Fin 4 → Fin 4 → ℝ) : Prop :=
  (∀ i, d i i = 0) ∧ (∀ i j, d i j = d j i) ∧ (∀ i j, 0 ≤ d i j) ∧
    (∀ i j k, d i k ≤ d i j + d j k)

/-- A four-point metric is *Ptolemaic* if every Ptolemy inequality holds. -/
def IsPtolemaic4 (d : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ x y z w, d x y * d z w ≤ d x z * d y w + d x w * d y z

/-- A four-point metric has *`q`-negative type*. -/
def HasNegType (q : ℝ) (d : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ c : Fin 4 → ℝ, ∑ i, c i = 0 → ∑ i, ∑ j, c i * c j * (d i j) ^ q ≤ 0

/-
**Key algebraic fact.** A symmetric `3×3` matrix
`[[A,u,v],[u,B,w],[v,w,C]]` with nonnegative diagonal entries, nonnegative
`2×2` principal minors, and nonnegative determinant defines a nonnegative
quadratic form.
-/
lemma psd3_of_minors (A B C u v w : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h01 : 0 ≤ A * B - u ^ 2) (h02 : 0 ≤ A * C - v ^ 2) (h12 : 0 ≤ B * C - w ^ 2)
    (hdet : 0 ≤ A * B * C + 2 * u * v * w - A * w ^ 2 - B * v ^ 2 - C * u ^ 2) :
    ∀ x y z : ℝ, 0 ≤ A * x ^ 2 + B * y ^ 2 + C * z ^ 2
      + 2 * u * x * y + 2 * v * x * z + 2 * w * y * z := by
  intro x y z
  by_cases hA' : A = 0
  · subst A
    have hu : u = 0 := by nlinarith [sq_nonneg u]
    have hv : v = 0 := by nlinarith [sq_nonneg v]
    subst u
    subst v
    by_cases hB' : B = 0
    · subst B
      have hw : w = 0 := by nlinarith [sq_nonneg w]
      subst w
      nlinarith [mul_nonneg hC (sq_nonneg z)]
    · cases lt_or_gt_of_ne hB' <;> nlinarith [sq_nonneg (B * y + w * z), sq_nonneg (C * z + w * y)]
  · -- Since $A > 0$, we can complete the square for the quadratic form.
    have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA')
    have h_complete_square : A * (A * x ^ 2 + B * y ^ 2 + C * z ^ 2 + 2 * u * x * y + 2 * v * x * z + 2 * w * y * z) = (A * x + u * y + v * z) ^ 2 + (B * A - u ^ 2) * y ^ 2 + (C * A - v ^ 2) * z ^ 2 + 2 * (w * A - u * v) * y * z := by
      ring
    have h_complete_square : (B * A - u ^ 2) * y ^ 2 + (C * A - v ^ 2) * z ^ 2 + 2 * (w * A - u * v) * y * z ≥ 0 := by
      have h_complete_square : (B * A - u ^ 2) * (C * A - v ^ 2) ≥ (w * A - u * v) ^ 2 := by
        nlinarith [hApos]
      by_cases h_case : B * A - u ^ 2 = 0
      · norm_num [show w * A - u * v = 0 by nlinarith] at *
        nlinarith [mul_self_nonneg z]
      · by_cases h_case : B * A - u ^ 2 > 0
        · nlinarith [sq_nonneg ((B * A - u ^ 2) * y + (w * A - u * v) * z), mul_self_pos.2 ‹_›]
        · exact False.elim <| h_case <| lt_of_le_of_ne (by linarith) <| Ne.symm ‹_›
    nlinarith [hApos]

/-
Elementary determinant form for star metrics: for `η₁₂, η₁₃, η₂₃ ∈ [0,1]`,
`1 - (η₁₂² + η₁₃² + η₂₃² + η₁₂ η₁₃ η₂₃)/4 ≥ 0`.
-/
lemma star_det_nonneg (a b c : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ 1 - (a ^ 2 + b ^ 2 + c ^ 2 + a * b * c) / 4 := by
  nlinarith [mul_nonneg ha0 hb0]

private lemma sqrt_pair_product (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a * b) * Real.sqrt (a * c) * Real.sqrt (b * c) = a * b * c := by
  rw [← Real.sqrt_mul (mul_nonneg ha hb),
    ← Real.sqrt_mul (mul_nonneg (mul_nonneg ha hb) (mul_nonneg ha hc))]
  rw [show a * b * (a * c) * (b * c) = (a * b * c) ^ 2 by ring]
  rw [Real.sqrt_sq (mul_nonneg (mul_nonneg ha hb) hc)]

private lemma rpow_mul_eq_sq_half (x y q : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ q * y ^ q = (x ^ (q / 2) * y ^ (q / 2)) ^ 2 := by
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx,
    ← Real.rpow_natCast, ← Real.rpow_mul hy]
  ring_nf

private lemma half_eta_sq_le (η S T : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hS0 : 0 ≤ S) (hSsq : S ^ 2 = T) :
    0 ≤ T - (η * S / 2) ^ 2 := by
  have hηS0 : 0 ≤ η * S := mul_nonneg hη0 hS0
  have hηS_le : η * S ≤ S := mul_le_of_le_one_left hS0 hη1
  nlinarith

/-
`3 ^ (log₃ 2) = 2`.
-/
lemma three_rpow_logb : (3 : ℝ) ^ (Real.logb 3 2) = 2 := by
  rw [Real.rpow_logb] <;> norm_num

/-
The upper exponent bound used throughout the `q ≥ 1` half is below `2`.
-/
lemma logb23_lt_two : Real.logb 2 3 < 2 := by
  rw [Real.logb_lt_iff_lt_rpow] <;> norm_num

lemma le_two_of_le_logb23 {q : ℝ} (hq : q ≤ Real.logb 2 3) : q ≤ 2 :=
  le_trans hq logb23_lt_two.le

/-
Numeric bounds: `1/2 < log₃ 2 < 2/3`.
-/
lemma logb32_bounds : 1 / 2 < Real.logb 3 2 ∧ Real.logb 3 2 < 2 / 3 := by
  rw [Real.logb]
  constructor <;> rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  all_goals norm_num [mul_comm, ← Real.log_rpow, Real.log_lt_log]

/-
The crossing function `Ξ(v) = (1+v+v²)/((1+2v)(2+v))` is antitone on `[0,1]`.
-/
lemma xi_antitoneOn :
    AntitoneOn (fun v : ℝ => (1 + v + v ^ 2) / ((1 + 2 * v) * (2 + v))) (Set.Icc (0 : ℝ) 1) := by
  intros v hv w hw hvw
  rw [div_le_div_iff₀] <;> nlinarith [hv.1, hv.2, hw.1, hw.2, mul_le_mul_of_nonneg_left hvw hv.1]

private lemma theta_deriv_eq (v : ℝ) (hv : 0 ≤ v) :
    deriv (fun v => Real.log (1 + v / 2)
        - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2)) v
      = (1 / (2 + v)) - (1 - Real.logb 3 2) * ((1 + 2 * v) / (1 + v + v ^ 2)) := by
  have hlog1 : HasDerivAt (fun x : ℝ => Real.log (1 + x / 2))
      ((1 / 2) / (1 + v / 2)) v := by
    have h := ((hasDerivAt_const v (1 : ℝ)).add ((hasDerivAt_id v).div_const 2)).log
      (by
        change 1 + v / 2 ≠ 0
        nlinarith [hv])
    simpa only [Pi.add_apply, id_eq, zero_add] using h
  have hquad : HasDerivAt (fun x : ℝ => 1 + x + x ^ 2) (1 + 2 * v) v := by
    have h := ((hasDerivAt_const v (1 : ℝ)).add (hasDerivAt_id v)).add
      (((hasDerivAt_id v).pow 2))
    have hfun : ((fun x : ℝ => 1) + id + id ^ 2) = (fun x : ℝ => 1 + x + x ^ 2) := by
      funext x
      change (1 : ℝ) + x + x ^ 2 = 1 + x + x ^ 2
      ring
    have hval : (0 : ℝ) + 1 + ((2 : ℕ) : ℝ) * id v ^ (2 - 1) * 1 = 1 + 2 * v := by
      norm_num
    rw [hfun, hval] at h
    exact h
  have hlog2 : HasDerivAt (fun x : ℝ => Real.log (1 + x + x ^ 2))
      ((1 + 2 * v) / (1 + v + v ^ 2)) v :=
    hquad.log (by nlinarith [hv])
  have hderiv := (hlog1.sub (hlog2.const_mul (1 - Real.logb 3 2))).deriv
  change deriv ((fun x : ℝ => Real.log (1 + x / 2)) -
      fun y => (1 - Real.logb 3 2) * Real.log (1 + y + y ^ 2)) v =
    1 / (2 + v) - (1 - Real.logb 3 2) * ((1 + 2 * v) / (1 + v + v ^ 2))
  rw [hderiv]
  field_simp [show 1 + v / 2 ≠ 0 by linarith, show 2 + v ≠ 0 by linarith,
    show 1 + v + v ^ 2 ≠ 0 by nlinarith [hv]]

/-
Core unimodality inequality: with `k₀ = 1 - log₃ 2 ∈ (1/3, 1/2)`,
the function `Θ(v) = log(1 + v/2) - k₀ · log(1 + v + v²)` is nonnegative on `[0,1]`.
It vanishes at the endpoints `v=0` and `v=1`, is increasing then decreasing.
-/
lemma theta_nonneg (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ Real.log (1 + v / 2) - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2) := by
  -- By the intermediate value theorem, there exists $v^* \in [0, 1]$ such that $\Xi(v^*) = k₀$.
  obtain ⟨v_star, hv_star⟩ : ∃ v_star ∈ Set.Icc (0 : ℝ) 1, (1 + v_star + v_star ^ 2) / ((1 + 2 * v_star) * (2 + v_star)) = 1 - Real.logb 3 2 := by
    apply_rules [intermediate_value_Icc'] <;> norm_num
    · exact ContinuousOn.div (Continuous.continuousOn (by continuity)) (Continuous.continuousOn (by continuity)) fun x hx => by nlinarith [hx.1, hx.2]
    · constructor <;> linarith [logb32_bounds]
  -- For $v \in [0, v^*]$, $\Xi(v) \geq \Xi(v^*) = k₀$ so $\Theta'(v) \geq 0$.
  have h_deriv_nonneg : ∀ v ∈ Set.Icc (0 : ℝ) v_star, 0 ≤ deriv (fun v => Real.log (1 + v / 2) - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2)) v := by
    intro v hv
    have h_deriv_nonneg : (1 + v + v ^ 2) / ((1 + 2 * v) * (2 + v)) ≥ 1 - Real.logb 3 2 := by
      rw [← hv_star.2]
      exact xi_antitoneOn (by constructor <;> linarith [hv.1, hv.2, hv_star.1.1, hv_star.1.2]) (by constructor <;> linarith [hv.1, hv.2, hv_star.1.1, hv_star.1.2]) hv.2
    rw [theta_deriv_eq v hv.1]
    rw [ge_iff_le] at h_deriv_nonneg
    rw [sub_nonneg, mul_div, div_le_div_iff₀ (show 0 < 1 + v + v ^ 2 by nlinarith [hv.1])
      (show 0 < 2 + v by nlinarith [hv.1])]
    have hnum : (1 - Real.logb 3 2) * ((1 + 2 * v) * (2 + v)) ≤ 1 + v + v ^ 2 :=
      (le_div_iff₀ (show 0 < (1 + 2 * v) * (2 + v) by nlinarith [hv.1])).mp h_deriv_nonneg
    nlinarith [hnum]
  -- For $v \in [v^*, 1]$, $\Xi(v) \leq k₀$ so $\Theta'(v) \leq 0$.
  have h_deriv_nonpos : ∀ v ∈ Set.Icc v_star 1, deriv (fun v => Real.log (1 + v / 2) - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2)) v ≤ 0 := by
    intro v hv
    have h_antitone : (1 + v + v ^ 2) / ((1 + 2 * v) * (2 + v)) ≤ (1 + v_star + v_star ^ 2) / ((1 + 2 * v_star) * (2 + v_star)) := by
      exact xi_antitoneOn (show v_star ∈ Set.Icc 0 1 from hv_star.1) (show v ∈ Set.Icc 0 1 from ⟨by linarith [hv.1, hv_star.1.1], by linarith [hv.2, hv_star.1.2]⟩) hv.1
    rw [theta_deriv_eq v (by linarith [hv.1, hv_star.1.1])]
    rw [hv_star.2] at h_antitone
    rw [sub_nonpos, mul_div, div_le_div_iff₀ (show 0 < 2 + v by nlinarith [hv.1, hv_star.1.1])
      (show 0 < 1 + v + v ^ 2 by nlinarith [hv.1, hv_star.1.1])]
    have hnum : 1 + v + v ^ 2 ≤ (1 - Real.logb 3 2) * ((1 + 2 * v) * (2 + v)) :=
      (div_le_iff₀ (show 0 < (1 + 2 * v) * (2 + v) by nlinarith [hv.1, hv_star.1.1])).mp h_antitone
    nlinarith [hnum]
  -- Therefore, $\Theta(v)$ is monotone nondecreasing on $[0, v^*]$ and nonincreasing on $[v^*, 1]$.
  have h_monotone : ∀ v ∈ Set.Icc (0 : ℝ) v_star, Real.log (1 + v / 2) - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2) ≥ Real.log (1 + 0 / 2) - (1 - Real.logb 3 2) * Real.log (1 + 0 + 0 ^ 2) := by
    intros v hv
    by_contra h_contra
    push Not at h_contra
    have := exists_deriv_eq_slope (f := fun v => Real.log (1 + v / 2) - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2)) (show v > 0 from hv.1.lt_of_ne (by rintro rfl; norm_num at h_contra))
    norm_num at *
    contrapose! this
    exact ⟨continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub (ContinuousAt.log (continuousAt_const.add (continuousAt_id.div_const _)) (by linarith [hx.1])) (ContinuousAt.mul continuousAt_const (ContinuousAt.log (continuousAt_const.add continuousAt_id |> ContinuousAt.add <| continuousAt_id.pow 2) (by nlinarith [hx.1]))), fun x hx => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.sub (DifferentiableAt.log (by norm_num) <| by linarith [hx.1]) <| DifferentiableAt.mul (differentiableAt_const _) <| DifferentiableAt.log (by norm_num [add_assoc]) <| by nlinarith [hx.1], fun c hc => by rw [ne_eq, eq_div_iff] <;> nlinarith [h_deriv_nonneg c (by linarith) (by linarith)]⟩
  have h_antitone : ∀ v ∈ Set.Icc v_star 1, Real.log (1 + v / 2) - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2) ≥ Real.log (1 + 1 / 2) - (1 - Real.logb 3 2) * Real.log (1 + 1 + 1 ^ 2) := by
    intros v hv
    by_contra h_contra
    have := exists_deriv_eq_slope (f := fun v => Real.log (1 + v / 2) - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2)) (show v < 1 from hv.2.lt_of_ne (by rintro rfl; norm_num at h_contra))
    norm_num at *
    contrapose! this
    refine ⟨?_, ?_, ?_⟩
    · exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub (ContinuousAt.log (continuousAt_const.add (continuousAt_id.div_const _)) (by nlinarith [hx.1, hx.2])) (ContinuousAt.mul continuousAt_const (ContinuousAt.log (continuousAt_const.add continuousAt_id |> ContinuousAt.add <| continuousAt_id.pow 2) (by nlinarith [hx.1, hx.2])))
    · exact fun x hx => DifferentiableAt.differentiableWithinAt (by exact DifferentiableAt.sub (DifferentiableAt.log (by norm_num) (by linarith [hx.1])) (DifferentiableAt.mul (differentiableAt_const _) (DifferentiableAt.log (by norm_num [add_assoc]) (by nlinarith [hx.1]))))
    · exact fun c hc => by rw [ne_eq, eq_div_iff] <;> nlinarith [h_deriv_nonpos c (by linarith) (by linarith)]
  by_cases hv : v ≤ v_star
  · exact le_trans (by norm_num) (h_monotone v ⟨hv0, hv⟩)
  · refine le_trans ?_ (h_antitone v ⟨by linarith, by linarith⟩)
    norm_num [Real.logb]
    rw [Real.log_div] <;> ring_nf <;> norm_num

/-
Key inequality behind `φ' ≥ 0`: for `t ≥ 1`,
`2·(t²+t+1)^(1-p₀) ≤ (2t+1)·t^(1-2p₀)` where `p₀ = log₃ 2`.
-/
lemma psi_key (t : ℝ) (ht : 1 ≤ t) :
    2 * (t ^ 2 + t + 1) ^ (1 - Real.logb 3 2)
      ≤ (2 * t + 1) * t ^ (1 - 2 * Real.logb 3 2) := by
  -- Apply the lemma `theta_nonneg` with $v = 1/t$ and $t = t$.
  have h_lemma : 0 ≤ Real.log (1 + 1 / (2 * t)) - (1 - Real.logb 3 2) * Real.log (1 + 1 / t + 1 / t^2) := by
    convert theta_nonneg (1 / t) (by positivity) (by rw [div_le_iff₀ (by positivity)]; linarith) using 1
    ring_nf
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity), Real.log_rpow (by positivity)]
  rw [show (t ^ 2 + t + 1 : ℝ) = t ^ 2 * (1 + 1 / t + 1 / t ^ 2) by nlinarith [one_div_mul_cancel (show t ≠ 0 by linarith), one_div_pow t 2], Real.log_mul (by positivity) (by positivity), Real.log_pow]
  ring_nf at *
  rw [show (1 + t * 2) = 2 * (1 + t⁻¹ * (1 / 2)) * t by nlinarith [mul_inv_cancel₀ (by linarith : t ≠ 0)], Real.log_mul, Real.log_mul] <;> first | positivity | ring_nf at *
  linarith [Real.log_pos one_lt_two]

private lemma star_phi_deriv_eq (t : ℝ) (ht : 0 < t) :
    deriv (fun t : ℝ => (t ^ 2 + t + 1) ^ (Real.logb 3 2) - t ^ (2 * Real.logb 3 2) - 1) t
      = Real.logb 3 2 *
        ((2 * t + 1) * (t ^ 2 + t + 1) ^ (Real.logb 3 2 - 1)
          - 2 * t ^ (2 * Real.logb 3 2 - 1)) := by
  have hquad : HasDerivAt (fun x : ℝ => x ^ 2 + x + 1) (2 * t + 1) t := by
    have h := (((hasDerivAt_id t).pow 2).add (hasDerivAt_id t)).add
      (hasDerivAt_const t (1 : ℝ))
    have hfun : (id ^ 2 + id + fun x : ℝ => 1) = (fun x : ℝ => x ^ 2 + x + 1) := by
      funext x
      change x ^ 2 + x + (1 : ℝ) = x ^ 2 + x + 1
      ring
    have hval : ((2 : ℕ) : ℝ) * id t ^ (2 - 1) * 1 + 1 + 0 = 2 * t + 1 := by
      norm_num
    rw [hfun, hval] at h
    exact h
  have hbase : t ^ 2 + t + 1 ≠ 0 := by nlinarith [ht]
  have h1 : HasDerivAt (fun x : ℝ => (x ^ 2 + x + 1) ^ Real.logb 3 2)
      ((2 * t + 1) * Real.logb 3 2 * (t ^ 2 + t + 1) ^ (Real.logb 3 2 - 1)) t :=
    hquad.rpow_const (Or.inl hbase)
  have h2 : HasDerivAt (fun x : ℝ => x ^ (2 * Real.logb 3 2))
      (1 * (2 * Real.logb 3 2) * t ^ (2 * Real.logb 3 2 - 1)) t :=
    (hasDerivAt_id t).rpow_const (Or.inl ht.ne')
  have hderiv := ((h1.sub h2).sub (hasDerivAt_const t (1 : ℝ))).deriv
  change deriv (((fun x : ℝ => (x ^ 2 + x + 1) ^ Real.logb 3 2) -
      (fun x : ℝ => x ^ (2 * Real.logb 3 2))) - fun _ => (1 : ℝ)) t =
    Real.logb 3 2 *
      ((2 * t + 1) * (t ^ 2 + t + 1) ^ (Real.logb 3 2 - 1)
        - 2 * t ^ (2 * Real.logb 3 2 - 1))
  rw [hderiv]
  ring

/-
The base case of the star inequality (single variable, exponent `p₀ = log₃ 2`).
For `t ≥ 0`, `t ^ (2 * log₃ 2) + 1 ≤ (t^2 + t + 1) ^ (log₃ 2)`.
-/
lemma star_single_p0 (t : ℝ) (ht : 0 ≤ t) :
    t ^ (2 * Real.logb 3 2) + 1 ≤ (t ^ 2 + t + 1) ^ (Real.logb 3 2) := by
  have h_deriv_nonneg : ∀ t : ℝ, 1 ≤ t → deriv (fun t : ℝ => (t^2 + t + 1) ^ (Real.logb 3 2) - t ^ (2 * Real.logb 3 2) - 1) t ≥ 0 := by
    intro t ht1
    have := psi_key t ht1
    rw [show (1 - Real.logb 3 2) = - (Real.logb 3 2 - 1) by ring, Real.rpow_neg (by positivity), show (1 - 2 * Real.logb 3 2) = - (2 * Real.logb 3 2 - 1) by ring, Real.rpow_neg (by positivity)] at this
    field_simp at this
    rw [star_phi_deriv_eq t (by linarith)]
    exact mul_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (sub_nonneg.mpr (by
      simpa [show t * (t + 1) + 1 = t ^ 2 + t + 1 by ring, mul_comm] using this))
  by_cases ht1 : t ≥ 1
  · -- For $t \geq 1$, we use the fact that $\phi'(t) \geq 0$ to show that $\phi(t)$ is non-decreasing.
    -- Since $\phi(t)$ is non-decreasing for $t \geq 1$, we have $\phi(t) \geq \phi(1)$.
    have h_phi_ge_phi1 : ∀ t : ℝ, 1 ≤ t → (t^2 + t + 1) ^ (Real.logb 3 2) - t ^ (2 * Real.logb 3 2) - 1 ≥ (1^2 + 1 + 1) ^ (Real.logb 3 2) - 1 ^ (2 * Real.logb 3 2) - 1 := by
      intro t ht
      by_contra h_contra
      push Not at h_contra
      have := exists_deriv_eq_slope (f := fun t : ℝ => (t^2 + t + 1) ^ Real.logb 3 2 - t ^ (2 * Real.logb 3 2) - 1) (show t > 1 from lt_of_le_of_ne ht <| Ne.symm <| by rintro rfl; norm_num at h_contra)
      norm_num at *
      contrapose! this
      exact ⟨ContinuousOn.sub (ContinuousOn.sub (ContinuousOn.rpow (ContinuousOn.add (ContinuousOn.add (continuousOn_id.pow 2) continuousOn_id) continuousOn_const) continuousOn_const <| by intro x hx; exact Or.inr <| by linarith [Real.logb_pos (show 3 > 1 by norm_num) (show 2 > 1 by norm_num)]) <| ContinuousOn.rpow continuousOn_id continuousOn_const <| by intro x hx; exact Or.inr <| by linarith [Real.logb_pos (show 3 > 1 by norm_num) (show 2 > 1 by norm_num)]) continuousOn_const, fun x hx => DifferentiableAt.differentiableWithinAt <| by norm_num [show x ^ 2 + x + 1 ≠ 0 from by nlinarith, show x ≠ 0 from by linarith [hx.1]], fun c hc => by rw [ne_eq, eq_div_iff] <;> nlinarith [h_deriv_nonneg c <| by linarith]⟩
    have := h_phi_ge_phi1 t ht1
    norm_num [Real.rpow_logb] at *
    linarith
  · by_cases ht0 : t = 0
    · norm_num [ht0, show Real.logb 3 2 ≠ 0 by exact ne_of_gt (Real.logb_pos (by norm_num) (by norm_num))]
    · -- For $0 < t < 1$, we use the symmetry argument.
      have h_symm : (t ^ 2 + t + 1) ^ (Real.logb 3 2) = t ^ (2 * Real.logb 3 2) * ((1 / t ^ 2 + 1 / t + 1) ^ (Real.logb 3 2)) := by
        rw [Real.rpow_mul] <;> norm_num [ht, ht0]
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        congr
        nlinarith [mul_inv_cancel₀ ht0, mul_inv_cancel₀ (pow_ne_zero 2 ht0)]
      -- By the properties of the function $\phi$, we know that $\phi(1/t) \geq 0$ for $t \geq 1$.
      have h_phi_inv : ∀ t : ℝ, 1 ≤ t → (t ^ 2 + t + 1) ^ (Real.logb 3 2) ≥ t ^ (2 * Real.logb 3 2) + 1 := by
        intro t ht1
        by_contra h_contra
        have := exists_deriv_eq_slope (f := fun t => (t ^ 2 + t + 1) ^ Real.logb 3 2 - t ^ (2 * Real.logb 3 2) - 1) (show t > 1 from ht1.lt_of_ne (by rintro rfl; norm_num at h_contra))
        norm_num at *
        contrapose! this
        exact ⟨ContinuousOn.sub (ContinuousOn.sub (ContinuousOn.rpow (ContinuousOn.add (ContinuousOn.add (continuousOn_id.pow 2) continuousOn_id) continuousOn_const) continuousOn_const <| by intro x hx; exact Or.inr <| by linarith [Real.logb_pos (show 3 > 1 by norm_num) (show 2 > 1 by norm_num)]) <| ContinuousOn.rpow continuousOn_id continuousOn_const <| by intro x hx; exact Or.inr <| by linarith [Real.logb_pos (show 3 > 1 by norm_num) (show 2 > 1 by norm_num)]) continuousOn_const, fun x hx => DifferentiableAt.differentiableWithinAt <| by norm_num [show x ^ 2 + x + 1 ≠ 0 from by nlinarith, show x ≠ 0 from by linarith [hx.1]], fun c hc => by rw [ne_eq, eq_div_iff] <;> nlinarith [h_deriv_nonneg c hc.1.le]⟩
      have := h_phi_inv (1 / t) (by rw [le_div_iff₀ (by positivity)]; linarith)
      simp_all +decide [division_def]
      rw [Real.inv_rpow (by positivity)] at this
      nlinarith [Real.rpow_pos_of_pos (show 0 < t by positivity) (2 * Real.logb 3 2), mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (show 0 < t by positivity) (2 * Real.logb 3 2)))]

/-
Monotonicity in the exponent: the single-variable star inequality for `p₀ = log₃ 2`
upgrades to all `p ∈ [log₃ 2, 1]`.
For `t ≥ 0` and `log₃ 2 ≤ p ≤ 1`, `t ^ (2*p) + 1 ≤ (t^2 + t + 1) ^ p`.
-/
lemma star_single {p t : ℝ} (hp0 : Real.logb 3 2 ≤ p) (_hp1 : p ≤ 1) (ht : 0 ≤ t) :
    t ^ (2 * p) + 1 ≤ (t ^ 2 + t + 1) ^ p := by
  by_cases ht1 : t ≤ 1
  · have h_monotone : t ^ (2 * p) + 1 ≤ (t ^ 2 + t + 1) ^ (Real.logb 3 2) := by
      have h_monotone : t ^ (2 * p) ≤ t ^ (2 * Real.logb 3 2) := by
        by_cases ht0 : t = 0
        · norm_num [ht0, show p ≠ 0 by linarith [Real.logb_pos (show (3 : ℝ) > 1 by norm_num) (show (2 : ℝ) > 1 by norm_num)], show Real.logb 3 2 ≠ 0 by exact ne_of_gt (Real.logb_pos (show (3 : ℝ) > 1 by norm_num) (show (2 : ℝ) > 1 by norm_num))]
        · exact Real.rpow_le_rpow_of_exponent_ge (by positivity) ht1 (by linarith)
      have h_monotone : t ^ (2 * Real.logb 3 2) + 1 ≤ (t ^ 2 + t + 1) ^ (Real.logb 3 2) := by
        convert star_single_p0 t ht using 1
      linarith
    exact h_monotone.trans (Real.rpow_le_rpow_of_exponent_le (by nlinarith) hp0)
  · -- For $t > 1$ and $p \ge \log_3 2$, we use the fact that $t^{2p} + 1 \le (t^2 + t + 1)^p$ follows from the monotonicity of the function $f(x) = x^p - x^{p₀}$ on $[1, \infty)$.
    have h_mono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → x^p - x^(Real.logb 3 2) ≤ y^p - y^(Real.logb 3 2) := by
      -- The derivative of $f(x) = x^p - x^{p₀}$ is $f'(x) = p x^{p-1} - p₀ x^{p₀-1}$.
      have h_deriv : ∀ x : ℝ, 1 ≤ x → deriv (fun x => x^p - x^(Real.logb 3 2)) x ≥ 0 := by
        intro x hx
        norm_num [show x ≠ 0 by linarith]
        ring_nf
        exact mul_le_mul hp0 (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (by positivity) (by linarith [Real.logb_nonneg (show 3 > 1 by norm_num) (show 2 ≥ 1 by norm_num)])
      intros x y hx hy
      by_contra h_contra
      push Not at h_contra
      have := exists_deriv_eq_slope (f := fun x => x ^ p - x ^ Real.logb 3 2) (show x < y from hy.lt_of_ne (by rintro rfl; linarith))
      norm_num at *
      exact absurd (this (by exact continuousOn_of_forall_continuousAt fun z hz => by exact ContinuousAt.sub (ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [hz.1]) (ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [hz.1])) (by exact fun z hz => by exact DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.sub (DifferentiableAt.rpow (differentiableAt_id) (by norm_num) <| by linarith [hz.1]) (DifferentiableAt.rpow (differentiableAt_id) (by norm_num) <| by linarith [hz.1]))) (by rintro ⟨c, ⟨hxc, hcy⟩, hcd⟩; rw [eq_div_iff] at hcd <;> nlinarith [h_deriv c <| by linarith])
    have := h_mono (t ^ 2) (t ^ 2 + t + 1) (by nlinarith) (by nlinarith)
    simp_all +decide [Real.rpow_mul]
    have := star_single_p0 t ht
    norm_num [Real.rpow_mul ht] at *
    linarith

/-
Two-variable homogeneous form of the star inequality.
For `log₃ 2 ≤ p ≤ 1` and `u, v ≥ 0`,
`u^p + v^p ≤ (u + v + Real.sqrt (u*v))^p`.
-/
lemma star_uv {p : ℝ} (hp0 : Real.logb 3 2 ≤ p) (hp1 : p ≤ 1)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u ^ p + v ^ p ≤ (u + v + Real.sqrt (u * v)) ^ p := by
  by_cases hu' : u = 0 <;> by_cases hv' : v = 0 <;> simp_all +decide [Real.sqrt_mul hu]
  · rw [Real.zero_rpow (by linarith [Real.logb_pos (show 3 > 1 by norm_num) (show 2 > 1 by norm_num)])]
  · rw [Real.zero_rpow (by linarith [Real.logb_pos (show 3 > 1 by norm_num) (show 2 > 1 by norm_num)])]
  · rw [Real.zero_rpow (by linarith [Real.logb_pos (show 3 > 1 by norm_num) (show 2 > 1 by norm_num)])]
  · -- Set $t := \sqrt{\frac{u}{v}} \geq 0$, so $t^2 = \frac{u}{v}$ and $\sqrt{uv} = v t$.
    obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ u = v * t^2 := by
      exact ⟨Real.sqrt (u / v), Real.sqrt_nonneg _, by rw [Real.sq_sqrt (div_nonneg hu hv), mul_div_cancel₀ _ hv']⟩
    -- Then $u^p + v^p = v^p (t^{2p} + 1)$ and $(u + v + \sqrt{uv})^p = v^p (t^2 + t + 1)^p$.
    have h_exp : u ^ p + v ^ p = v ^ p * (t ^ (2 * p) + 1) ∧ (u + v + Real.sqrt (u * v)) ^ p = v ^ p * (t ^ 2 + t + 1) ^ p := by
      constructor <;> ring_nf
      · rw [ht.2, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        ring_nf
      · rw [← Real.mul_rpow (by positivity) (by nlinarith)]
        rw [ht.2]
        ring_nf
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_sq (by linarith)]
        ring_nf
    rw [← Real.sqrt_mul hu]
    exact h_exp.1.symm ▸ h_exp.2.symm ▸ mul_le_mul_of_nonneg_left (star_single hp0 hp1 ht.1) (by positivity)

/-
**Star inequality** (Lemma `lem:q5-star`).
For `1 ≤ q ≤ log₂ 3` and `a, b ≥ 0`,
`(a + b)^q ≤ a^q + b^q + (a*b)^(q/2)`.
-/
lemma star_inequality {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ q ≤ a ^ q + b ^ q + (a * b) ^ (q / 2) := by
  -- Set $p := 1 / q$.
  set p := 1 / q with hp
  -- Apply star_uv with this p, u := a^q, v := b^q (both ≥ 0).
  have h_star_uv : (a^q)^p + (b^q)^p ≤ (a^q + b^q + Real.sqrt ((a^q) * (b^q)))^p := by
    convert star_uv _ _ _ _ (Real.rpow_nonneg ha q) (Real.rpow_nonneg hb q) using 1 <;> ring_nf
    · rw [Real.logb, div_le_div_iff₀] <;> norm_num
      · rw [Real.logb] at hq
        rw [le_div_iff₀ (Real.log_pos (by norm_num))] at hq
        linarith
      · positivity
      · linarith
    · exact div_le_self zero_le_one hq1
  convert Real.rpow_le_rpow _ h_star_uv (show 0 ≤ q by positivity) using 1
  · rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_one_div_cancel (by positivity), Real.rpow_one, Real.rpow_one]
  · rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (by positivity), Real.rpow_one]
    rw [← Real.mul_rpow (by positivity) (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    ring_nf
  · positivity

private lemma star_pair_data {q x y : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ η S : ℝ,
      0 ≤ η ∧ η ≤ 1 ∧ 0 ≤ S ∧
      (x + y) ^ q = x ^ q + y ^ q + η * S ∧
      S ^ 2 = x ^ q * y ^ q ∧
      S = Real.sqrt (x ^ q * y ^ q) := by
  refine ⟨((x + y) ^ q - x ^ q - y ^ q) / Real.sqrt (x ^ q * y ^ q),
    Real.sqrt (x ^ q * y ^ q), ?_, ?_, Real.sqrt_nonneg _, ?_, ?_, rfl⟩
  · refine div_nonneg ?_ (Real.sqrt_nonneg _)
    have := @Real.add_rpow_le_rpow_add
    linarith [this hx hy hq1]
  · refine div_le_one_of_le₀ ?_ (Real.sqrt_nonneg _)
    have := star_inequality hq1 hq x y hx hy
    rw [Real.mul_rpow (by positivity) (by positivity)] at this
    rw [rpow_mul_eq_sq_half x y q hx hy, Real.sqrt_sq (by positivity)]
    linarith
  · by_cases h : Real.sqrt (x ^ q * y ^ q) = 0
    · have hprod : x ^ q * y ^ q = 0 := (Real.sqrt_eq_zero (by positivity)).mp h
      rcases mul_eq_zero.mp hprod with hxpow | hypow
      · have hx0 : x = 0 := ((Real.rpow_eq_zero_iff_of_nonneg hx).mp hxpow).1
        rw [hx0]
        simp [Real.zero_rpow (by linarith : q ≠ 0)]
      · have hy0 : y = 0 := ((Real.rpow_eq_zero_iff_of_nonneg hy).mp hypow).1
        rw [hy0]
        simp [Real.zero_rpow (by linarith : q ≠ 0)]
    · field_simp [h]
      ring
  · rw [Real.sq_sqrt (by positivity)]

/-! ## Schoenberg reduction and the supporting metric lemmas -/

/-
**Reduction to a positive semidefinite Schoenberg matrix.**
If the `3×3` Schoenberg quadratic form at base point `3` is nonnegative on all
vectors `(a₀,a₁,a₂)`, then the four-point metric `d` has `q`-negative type.
-/
lemma negType_of_schoenberg {q : ℝ} (hq0 : 0 < q) (d : Fin 4 → Fin 4 → ℝ)
    (hsymm : ∀ i j, d i j = d j i) (hdiag : ∀ i, d i i = 0)
    (hPSD : ∀ a0 a1 a2 : ℝ,
      0 ≤ a0 ^ 2 * d 0 3 ^ q + a1 ^ 2 * d 1 3 ^ q + a2 ^ 2 * d 2 3 ^ q
        + 2 * a0 * a1 * ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2)
        + 2 * a0 * a2 * ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2)
        + 2 * a1 * a2 * ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2)) :
    HasNegType q d := by
  intro c hc
  simp_all +decide [Fin.sum_univ_four]
  rw [show c 3 = -c 0 - c 1 - c 2 by linarith]
  ring_nf at *
  norm_num [hq0.ne']
  linarith [hPSD (c 0) (c 1) (c 2)]

/-
**`2×2` minor nonnegativity** (snowflaked triangle is Euclidean).
For `0 < q ≤ 2` and a triangle with side lengths `p, r, s`,
`p^q · r^q - ((p^q + r^q - s^q)/2)^2 ≥ 0`.
-/
lemma minor_nonneg {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2) (p r s : ℝ)
    (hp : 0 ≤ p) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h1 : s ≤ p + r) (h2 : p ≤ s + r) (h3 : r ≤ s + p) :
    0 ≤ p ^ q * r ^ q - ((p ^ q + r ^ q - s ^ q) / 2) ^ 2 := by
  -- Set $X := p^{q/2}$, $Y := r^{q/2}$, $Z := s^{q/2}$, all ≥ 0.
  set X := p ^ (q / 2)
  set Y := r ^ (q / 2)
  set Z := s ^ (q / 2)
  -- Then $p^q = X^2$, $r^q = Y^2$, $s^q = Z^2$ (since $(p^{q/2})^2 = p^{(q/2)*2} = p^q$, using Real.rpow_natCast / Real.rpow_mul with $p \geq 0$).
  have hX : X^2 = p^q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp]
    ring_nf
  have hY : Y^2 = r^q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
    ring_nf
  have hZ : Z^2 = s^q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    ring_nf
  -- We show the snowflaked triangle inequalities, i.e. each factor ≥ 0:
  have hX_Y_Z : X + Y - Z ≥ 0 ∧ Z + X - Y ≥ 0 ∧ Z + Y - X ≥ 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> norm_num
    · exact le_trans (Real.rpow_le_rpow (by positivity) h1 (by positivity)) (by simpa using Real.rpow_add_le_add_rpow (by positivity) (by positivity) (by positivity) (by linarith))
    · exact le_trans (Real.rpow_le_rpow (by positivity) (by linarith : r ≤ s + p) (by positivity)) (by simpa using Real.rpow_add_le_add_rpow hs hp (by positivity) (by linarith))
    · exact le_trans (Real.rpow_le_rpow (by positivity) (show p ≤ s + r by linarith) (by positivity)) (by simpa using Real.rpow_add_le_add_rpow (by positivity) (by positivity) (by positivity) (by linarith))
  nlinarith [mul_nonneg hX_Y_Z.1 (mul_nonneg hX_Y_Z.2.1 hX_Y_Z.2.2)]

/-
**Line metrics give negative type** (the result proved in `Main`, transported to
`Fin 4` via an embedding into `ℝ`).
If `d i j = |x i - x j|` for some `x : Fin 4 → ℝ`, then `d` has `q`-negative type
for `0 < q ≤ 2`.
-/
lemma embed_real_negType {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2)
    (x : Fin 4 → ℝ) (c : Fin 4 → ℝ) (hc : ∑ i, c i = 0) :
    ∑ i, ∑ j, c i * c j * |x i - x j| ^ q ≤ 0 := by
  -- Define the grouped weight w : ℝ → ℝ by w v := ∑ i ∈ Finset.univ.filter (fun i => x i = v), c i.
  set w : ℝ → ℝ := fun v => ∑ i ∈ Finset.univ.filter (fun i => x i = v), c i
  -- Claim 2: $\sum_{i,j} c_i c_j |x_i - x_j|^q = \sum_{v,u} w(v) w(u) |v - u|^q$.
  have h_sum : ∑ i, ∑ j, c i * c j * |x i - x j| ^ q = ∑ v ∈ Finset.image x Finset.univ, ∑ u ∈ Finset.image x Finset.univ, w v * w u * |v - u| ^ q := by
    simp +zetaDelta at *
    simp +decide only [Finset.sum_sigma', Finset.univ_sigma_univ, Finset.sum_mul _ _ _, Finset.mul_sum]
    refine Finset.sum_bij (fun i hi => ⟨x i.fst, x i.snd, i.fst, i.snd⟩) ?_ ?_ ?_ ?_ <;> aesop
  -- By NegType.real_finite_negative_type hq0 hq2 S w (Claim 1), the RHS ≤ 0, hence the LHS ≤ 0 by Claim 2.
  apply h_sum.symm ▸ NegType.real_finite_negative_type hq0 hq2 (Finset.image x Finset.univ) w (by
    rw [← hc, Finset.sum_image' c]
    intro i _
    simp [w])

/-- **Line metrics have negative type** (`lem:q5-line-metrics`).
If the four-point metric `d` is realised on a line (`d i j = |x i - x j|`), then
`d` has `q`-negative type for `0 < q ≤ 2`. -/
lemma line_negType {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2)
    (d : Fin 4 → Fin 4 → ℝ) (x : Fin 4 → ℝ) (hx : ∀ i j, d i j = |x i - x j|) :
    HasNegType q d := by
  intro c hc
  have := embed_real_negType hq0 hq2 x c hc
  simpa only [hx] using this

/-
**Star metrics have negative type** (`lem:q5-star-metrics`).
A four-point star metric with centre `3` and leaves `0,1,2` (so the leaf–leaf
distance equals the sum of the two leaf lengths) has `q`-negative type for
`1 ≤ q ≤ log₂ 3`.
-/
lemma star_negType {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d)
    (h01 : d 0 1 = d 0 3 + d 1 3) (h02 : d 0 2 = d 0 3 + d 2 3)
    (h12 : d 1 2 = d 1 3 + d 2 3) :
    HasNegType q d := by
  refine negType_of_schoenberg ?_ ?_ ?_ ?_ ?_
  · linarith
  · exact hm.2.1
  · exact hm.1
  · intro a0 a1 a2
    set ρ0 := d 0 3
    set ρ1 := d 1 3
    set ρ2 := d 2 3
    have hρ0 : 0 ≤ ρ0 := by
      exact hm.2.2.1 _ _
    have hρ1 : 0 ≤ ρ1 := by
      exact hm.2.2.1 _ _
    have hρ2 : 0 ≤ ρ2 := by
      exact hm.2.2.1 _ _
    -- Pairwise star data for the three leaf pairs.
    obtain ⟨η01, S01, hη01_nonneg, hη01_le_one, hS01_nonneg,
      hρ01, hS01_sq, hS01_eq⟩ := star_pair_data hq1 hq hρ0 hρ1
    obtain ⟨η02, S02, hη02_nonneg, hη02_le_one, hS02_nonneg,
      hρ02, hS02_sq, hS02_eq⟩ := star_pair_data hq1 hq hρ0 hρ2
    obtain ⟨η12, S12, hη12_nonneg, hη12_le_one, hS12_nonneg,
      hρ12, hS12_sq, hS12_eq⟩ := star_pair_data hq1 hq hρ1 hρ2
    have hS_prod : S01 * S02 * S12 = ρ0 ^ q * ρ1 ^ q * ρ2 ^ q := by
      rw [hS01_eq, hS02_eq, hS12_eq]
      exact sqrt_pair_product (ρ0 ^ q) (ρ1 ^ q) (ρ2 ^ q)
        (Real.rpow_nonneg hρ0 _) (Real.rpow_nonneg hρ1 _) (Real.rpow_nonneg hρ2 _)
    -- Apply psd3_of_minors with the given conditions.
    have h_psd : 0 ≤ ρ0 ^ q * ρ1 ^ q - (η01 * S01 / 2) ^ 2 ∧ 0 ≤ ρ0 ^ q * ρ2 ^ q - (η02 * S02 / 2) ^ 2 ∧ 0 ≤ ρ1 ^ q * ρ2 ^ q - (η12 * S12 / 2) ^ 2 ∧ 0 ≤ ρ0 ^ q * ρ1 ^ q * ρ2 ^ q * (1 - (η01 ^ 2 + η02 ^ 2 + η12 ^ 2 + η01 * η02 * η12) / 4) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact half_eta_sq_le η01 S01 (ρ0 ^ q * ρ1 ^ q)
          hη01_nonneg hη01_le_one hS01_nonneg hS01_sq
      · exact half_eta_sq_le η02 S02 (ρ0 ^ q * ρ2 ^ q)
          hη02_nonneg hη02_le_one hS02_nonneg hS02_sq
      · exact half_eta_sq_le η12 S12 (ρ1 ^ q * ρ2 ^ q)
          hη12_nonneg hη12_le_one hS12_nonneg hS12_sq
      · refine mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hρ0 _) (Real.rpow_nonneg hρ1 _)) (Real.rpow_nonneg hρ2 _)) ?_
        exact star_det_nonneg η01 η02 η12 hη01_nonneg hη01_le_one
          hη02_nonneg hη02_le_one hη12_nonneg hη12_le_one
    rw [h01, h02, h12]
    rw [hρ01, hρ02, hρ12]
    convert psd3_of_minors (ρ0 ^ q) (ρ1 ^ q) (ρ2 ^ q) (- (η01 * S01 / 2)) (- (η02 * S02 / 2)) (- (η12 * S12 / 2)) (by positivity) (by positivity) (by positivity) _ _ _ _ a0 a1 a2 using 1
    · ring_nf
    · simpa using h_psd.1
    · simpa using h_psd.2.1
    · simpa using h_psd.2.2.1
    · convert h_psd.2.2.2 using 1
      ring_nf
      rw [hS01_sq, hS02_sq, hS12_sq]
      rw [show η01 * S01 * η02 * S02 * η12 * S12 =
          η01 * η02 * η12 * (S01 * S02 * S12) by ring]
      rw [hS_prod]
      ring_nf

/-- The Schoenberg determinant (based at `3`), as an explicit function of the
six entries. -/
def schoenDet (A B C u v w : ℝ) : ℝ :=
  A * B * C + 2 * u * v * w - A * w ^ 2 - B * v ^ 2 - C * u ^ 2

/-
**One-entry concavity** (`lem:q5-one-entry-concavity`): `schoenDet` is a concave
quadratic in the entry `u` (with leading coefficient `-C ≤ 0`), so if it is
nonnegative at two values `u₁, u₂` of `u` it is nonnegative at every value between.
-/
lemma schoenDet_ge_of_endpoints (A B C v w : ℝ) (hC : 0 ≤ C) (u u1 u2 : ℝ)
    (hu1 : u1 ≤ u) (hu2 : u ≤ u2)
    (h1 : 0 ≤ schoenDet A B C u1 v w) (h2 : 0 ≤ schoenDet A B C u2 v w) :
    0 ≤ schoenDet A B C u v w := by
  by_cases hu : u1 = u2
  · subst u2
    have hu_eq : u = u1 := le_antisymm hu2 hu1
    subst u
    exact h1
  · unfold schoenDet at *
    cases lt_or_gt_of_ne hu <;> nlinarith [mul_le_mul_of_nonneg_left hu1 hC, mul_le_mul_of_nonneg_left hu2 hC, mul_le_mul_of_nonneg_left hu1 (sub_nonneg.mpr hu2), mul_le_mul_of_nonneg_left hu2 (sub_nonneg.mpr hu1)]

/-
**Reverse Schoenberg direction**: if `d` has `q`-negative type, then the
Schoenberg determinant based at `3` is nonnegative.
-/
lemma det_nonneg_of_negType {q : ℝ} (hq0 : 0 < q) (d : Fin 4 → Fin 4 → ℝ)
    (hsymm : ∀ i j, d i j = d j i) (hdiag : ∀ i, d i i = 0) (hneg : HasNegType q d) :
    0 ≤ schoenDet (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q)
        ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2)
        ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2)
        ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2) := by
  -- Consider the symmetric 3 × 3 matrix M = !![A, u, v; u, B, w; v, w, C].
  set A := d 0 3 ^ q
  set B := d 1 3 ^ q
  set C := d 2 3 ^ q
  set u := (A + B - d 0 1 ^ q) / 2
  set v := (A + C - d 0 2 ^ q) / 2
  set w := (B + C - d 1 2 ^ q) / 2
  -- By definition of $A$, $B$, $C$, $u$, $v$, and $w$, we know that $M$ is positive semidefinite.
  have hM_posSemidef : ∀ x y z : ℝ, 0 ≤ A * x ^ 2 + B * y ^ 2 + C * z ^ 2 + 2 * u * x * y + 2 * v * x * z + 2 * w * y * z := by
    intro x y z
    specialize hneg (fun i => if i = 0 then x else if i = 1 then y else if i = 2 then z else -(x + y + z)) (by
      simp +decide [Fin.sum_univ_four])
    simp +decide [Fin.sum_univ_four] at hneg
    simp_all +decide [ne_of_gt hq0]
    grind
  -- Since $M$ is positive semidefinite, its determinant is nonnegative.
  have hM_det_nonneg : Matrix.PosSemidef (Matrix.of ![![A, u, v], ![u, B, w], ![v, w, C]]) := by
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · intro x
      convert hM_posSemidef (x 0) (x 1) (x 2) using 1
      · rfl
      · simp +decide [Finsupp.sum_fintype, Fin.sum_univ_three]
        ring
  convert hM_det_nonneg.det_nonneg using 1 <;> try rfl
  · norm_num [Matrix.det_fin_three]
    unfold schoenDet
    simp +decide
    ring

/-- The Schoenberg determinant of any four points on a line is nonnegative. -/
lemma line_schoenDet_nonneg {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2) (x : Fin 4 → ℝ) :
    0 ≤ schoenDet (|x 0 - x 3| ^ q) (|x 1 - x 3| ^ q) (|x 2 - x 3| ^ q)
        ((|x 0 - x 3| ^ q + |x 1 - x 3| ^ q - |x 0 - x 1| ^ q) / 2)
        ((|x 0 - x 3| ^ q + |x 2 - x 3| ^ q - |x 0 - x 2| ^ q) / 2)
        ((|x 1 - x 3| ^ q + |x 2 - x 3| ^ q - |x 1 - x 2| ^ q) / 2) := by
  exact det_nonneg_of_negType hq0 (fun i j => |x i - x j|)
    (fun i j => abs_sub_comm _ _) (fun i => by simp)
    (line_negType hq0 hq2 _ x (fun _ _ => rfl))

/-
Negative type is invariant under relabelling the four points.
-/
lemma hasNegType_reindex {q : ℝ} {d : Fin 4 → Fin 4 → ℝ} (σ : Equiv.Perm (Fin 4))
    (h : HasNegType q d) : HasNegType q (fun i j => d (σ i) (σ j)) := by
  intro c hc
  -- Set c' := fun k => c (σ⁻¹ k).
  set c' : Fin 4 → ℝ := fun k => c (σ⁻¹ k)
  convert h c' _ using 1
  · convert rfl using 1
    conv_rhs => rw [← Equiv.sum_comp σ⁻¹]
    exact Finset.sum_congr rfl fun i hi => by rw [← Equiv.sum_comp σ]; aesop
  · exact hc ▸ Equiv.sum_comp σ⁻¹ c

/-
**Inversion is a diagonal congruence** of the Schoenberg matrix: scaling row/column
`i` by `Di` multiplies the determinant by `(D0 D1 D2)^2`.
-/
lemma schoenDet_congr (D0 D1 D2 A B C u v w : ℝ) :
    schoenDet (D0 ^ 2 * A) (D1 ^ 2 * B) (D2 ^ 2 * C)
        (D0 * D1 * u) (D0 * D2 * v) (D1 * D2 * w)
      = (D0 * D1 * D2) ^ 2 * schoenDet A B C u v w := by
  unfold schoenDet
  ring

/-! ### Leaf-permutation symmetry of `schoenDet`

`schoenDet` is the determinant of the symmetric `3×3` matrix
`!![A, u, v; u, B, w; v, w, C]`, so it is invariant under simultaneously permuting
the diagonal entries `(A,B,C)` (the leaf lengths) and the corresponding off-diagonal
entries.  Each transposition is purely algebraic.  These let a boundary configuration
arriving under a relabelling of the leaves be matched to the fixed-labelling endpoint
lemmas (`endpoint_star_det`, `endpoint_line_det`, `geodesic_ptolemy_endpoint_det`). -/

/-- Swapping leaves `0 ↔ 1`. -/
lemma schoenDet_swap01 (A B C u v w : ℝ) :
    schoenDet B A C u w v = schoenDet A B C u v w := by
  unfold schoenDet
  ring

/-- Swapping leaves `1 ↔ 2`. -/
lemma schoenDet_swap12 (A B C u v w : ℝ) :
    schoenDet A C B v u w = schoenDet A B C u v w := by
  unfold schoenDet
  ring

/-- Swapping leaves `0 ↔ 2`. -/
lemma schoenDet_swap02 (A B C u v w : ℝ) :
    schoenDet C B A w v u = schoenDet A B C u v w := by
  unfold schoenDet
  ring

/-- **Distance-parameterised concavity reduction** for the first off-diagonal slot.
The entry `(A + B - t^q)/2` is a decreasing function of the distance `t` (since
`t ↦ t^q` is increasing for `q > 0`), so as `t` ranges over `[t1, t2]` the entry
ranges over an interval and `schoenDet` is concave there.  Hence if the determinant
is nonnegative at the two distance-endpoints `t1, t2`, it is nonnegative at `t`. -/
lemma schoenDet_reduce_dist {q : ℝ} (hq0 : 0 < q) (A B C v w : ℝ) (hC : 0 ≤ C)
    (t t1 t2 : ℝ) (ht1 : 0 ≤ t1) (ht1' : t1 ≤ t) (ht2 : t ≤ t2)
    (h1 : 0 ≤ schoenDet A B C ((A + B - t1 ^ q) / 2) v w)
    (h2 : 0 ≤ schoenDet A B C ((A + B - t2 ^ q) / 2) v w) :
    0 ≤ schoenDet A B C ((A + B - t ^ q) / 2) v w := by
  have hmono1 : t1 ^ q ≤ t ^ q := Real.rpow_le_rpow ht1 ht1' hq0.le
  have hmono2 : t ^ q ≤ t2 ^ q := Real.rpow_le_rpow (ht1.trans ht1') ht2 hq0.le
  exact schoenDet_ge_of_endpoints A B C v w hC ((A + B - t ^ q) / 2)
    ((A + B - t2 ^ q) / 2) ((A + B - t1 ^ q) / 2) (by linarith) (by linarith) h2 h1

/-- A nonnegative base-`3` Schoenberg determinant, together with the metric triangle
inequalities, gives `q`-negative type. -/
lemma negType_of_schoenDet_nonneg {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d)
    (hdet : 0 ≤ schoenDet (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q)
        ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2)
        ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2)
        ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2)) :
    HasNegType q d := by
  apply negType_of_schoenberg hq0 d hm.2.1 hm.1
  intro a0 a1 a2
  unfold schoenDet at hdet
  nlinarith [psd3_of_minors (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q)
    ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2)
    ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2)
    ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2)
    (Real.rpow_nonneg (hm.2.2.1 _ _) _) (Real.rpow_nonneg (hm.2.2.1 _ _) _)
    (Real.rpow_nonneg (hm.2.2.1 _ _) _)
    (minor_nonneg hq0 hq2 (d 0 3) (d 1 3) (d 0 1)
      (hm.2.2.1 _ _) (hm.2.2.1 _ _) (hm.2.2.1 _ _)
      (by linarith [hm.2.2.2 0 3 1, hm.2.1 3 1]) (by linarith [hm.2.2.2 0 1 3])
      (by linarith [hm.2.2.2 1 0 3, hm.2.1 1 0]))
    (minor_nonneg hq0 hq2 (d 0 3) (d 2 3) (d 0 2)
      (hm.2.2.1 _ _) (hm.2.2.1 _ _) (hm.2.2.1 _ _)
      (by linarith [hm.2.2.2 0 3 2, hm.2.1 3 2]) (by linarith [hm.2.2.2 0 2 3])
      (by linarith [hm.2.2.2 2 0 3, hm.2.1 2 0]))
    (minor_nonneg hq0 hq2 (d 1 3) (d 2 3) (d 1 2)
      (hm.2.2.1 _ _) (hm.2.2.1 _ _) (hm.2.2.1 _ _)
      (by linarith [hm.2.2.2 1 3 2, hm.2.1 3 2]) (by linarith [hm.2.2.2 1 2 3])
      (by linarith [hm.2.2.2 2 1 3, hm.2.1 2 1]))
    hdet a0 a1 a2]

/-- **Concavity in the apex-distance entry.** When the apex distance `C` (between the
base point and the third leaf) varies, it enters `schoenDet` through the diagonal entry
`C` *and* the two off-diagonal entries `(A+C-p)/2`, `(B+C-r)/2`.  The result is a
quadratic in `C` with leading coefficient `(2u - A - B)/4 ≤ 0` (since `u ≤ (A+B)/2`),
hence concave.  So if the determinant is nonnegative at the endpoints `C1, C2` of a
feasible interval, it is nonnegative throughout.  This lets the apex distance be reduced
*without reindexing*, keeping the other (Ptolemaic) distances fixed. -/
lemma schoenDet_concave_apex (A B p r u : ℝ) (hu : 2 * u ≤ A + B)
    (C C1 C2 : ℝ) (h1 : C1 ≤ C) (h2 : C ≤ C2)
    (he1 : 0 ≤ schoenDet A B C1 u ((A + C1 - p) / 2) ((B + C1 - r) / 2))
    (he2 : 0 ≤ schoenDet A B C2 u ((A + C2 - p) / 2) ((B + C2 - r) / 2)) :
    0 ≤ schoenDet A B C u ((A + C - p) / 2) ((B + C - r) / 2) := by
  by_cases hC : C1 = C2
  · have : C = C2 := le_antisymm h2 (hC ▸ h1)
    rw [this]
    exact he2
  · have hlt : C1 < C2 := lt_of_le_of_ne (h1.trans h2) hC
    unfold schoenDet at he1 he2 ⊢
    nlinarith [mul_nonneg he1 (sub_nonneg.mpr h2), mul_nonneg he2 (sub_nonneg.mpr h1),
      mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h1))
        (by linarith : (0 : ℝ) ≤ A + B - 2 * u)) (le_of_lt (sub_pos.mpr hlt)),
      sub_pos.mpr hlt]


/-
The Schoenberg determinant (based at the apex `A`, with leaf lengths `y` to `A`,
`r = PU`, `z = PV`) of the **star** endpoint `h = r + z` of an attached-ray
configuration is nonnegative. Here the four points form a star with centre `P`.
-/
lemma endpoint_star_det {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (y r z : ℝ) (hy : 0 ≤ y) (hr : 0 ≤ r) (hz : 0 ≤ z) :
    0 ≤ schoenDet (y ^ q) ((y + r) ^ q) ((y + z) ^ q)
        ((y ^ q + (y + r) ^ q - r ^ q) / 2)
        ((y ^ q + (y + z) ^ q - z ^ q) / 2)
        (((y + r) ^ q + (y + z) ^ q - (r + z) ^ q) / 2) := by
  set dS : Fin 4 → Fin 4 → ℝ := fun i j => if i = j then 0 else (if i = 0 then 0 else if i = 1 then r else if i = 2 then z else y) + (if j = 0 then 0 else if j = 1 then r else if j = 2 then z else y)
  set dC : Fin 4 → Fin 4 → ℝ := fun i j => if i = j then 0 else (if i = 0 then y else if i = 1 then r else if i = 2 then z else 0) + (if j = 0 then y else if j = 1 then r else if j = 2 then z else 0)
  have h_center_negType : HasNegType q dC := by
    apply star_negType hq1 hq
    · refine ⟨fun _ => if_pos rfl, ?_, ?_, ?_⟩
      · intro i j
        fin_cases i <;> fin_cases j <;> simp [dC, add_comm]
      · intro i j
        fin_cases i <;> fin_cases j <;> simp [dC, hy, hr, hz] <;> linarith
      · intro i j k
        fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [dC] <;> linarith [hy, hr, hz]
    · simp [dC]
    · simp [dC]
    · simp [dC]
  have h_star_negType : HasNegType q dS := by
    set σ : Equiv.Perm (Fin 4) := Equiv.swap 0 3
    convert hasNegType_reindex σ h_center_negType using 1
    exact funext fun i => funext fun j => by fin_cases i <;> fin_cases j <;> simp [dS, dC, σ, Equiv.swap_apply_def]
  convert det_nonneg_of_negType (show 0 < q by linarith) dS _ _ h_star_negType using 1
  · simp [dS]
    ring_nf
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [dS, add_comm]
  · exact fun i => if_pos rfl

/-
The Schoenberg determinant of the **line** endpoint `h = |r - z|` of an
attached-ray configuration is nonnegative (the four points are collinear).
-/
lemma endpoint_line_det {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2)
    (y r z : ℝ) (hy : 0 ≤ y) (hr : 0 ≤ r) (hz : 0 ≤ z) :
    0 ≤ schoenDet (y ^ q) ((y + r) ^ q) ((y + z) ^ q)
        ((y ^ q + (y + r) ^ q - r ^ q) / 2)
        ((y ^ q + (y + z) ^ q - z ^ q) / 2)
        (((y + r) ^ q + (y + z) ^ q - |r - z| ^ q) / 2) := by
  convert det_nonneg_of_negType hq0 (fun i j ↦ |(if i = 3 then 0 else if i = 0 then y else if i = 1 then y + r else y + z) - (if j = 3 then 0 else if j = 0 then y else if j = 1 then y + r else y + z)|) _ _ _ using 1 <;> norm_num
  · simp +decide [abs_of_nonneg, hy, hr, hz]
    rw [abs_of_nonneg (by positivity : 0 ≤ y + r), abs_of_nonneg (by positivity : 0 ≤ y + z)]
  · exact fun i j => abs_sub_comm _ _
  · exact line_negType hq0 hq2 _ _ fun i j => rfl

/-
**Attached-ray extension** (`lem:q5-attached-ray`).
With apex `A = 3` and `P = 0, U = 1, V = 2`, if `d 1 3 = d 0 3 + d 0 1`
(i.e. `AU = AP + PU`) and `d 2 3 = d 0 3 + d 0 2` (i.e. `AV = AP + PV`), then
`d` has `q`-negative type for `1 ≤ q ≤ log₂ 3`.
-/
lemma attached_ray_negType {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d)
    (hU : d 1 3 = d 0 3 + d 0 1) (hV : d 2 3 = d 0 3 + d 0 2) :
    HasNegType q d := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hq2 : q ≤ 2 := le_two_of_le_logb23 hq
  have hnn := hm.2.2.1
  have h_det_nonneg : 0 ≤ schoenDet (d 2 3 ^ q) (d 1 3 ^ q) (d 0 3 ^ q) (((d 2 3 ^ q + d 1 3 ^ q - d 1 2 ^ q) / 2)) (((d 2 3 ^ q + d 0 3 ^ q - d 0 2 ^ q) / 2)) (((d 1 3 ^ q + d 0 3 ^ q - d 0 1 ^ q) / 2)) := by
    apply schoenDet_ge_of_endpoints
    · exact Real.rpow_nonneg (hnn _ _) _
    rotate_left
    rotate_left
    rotate_left
    rotate_left
    exact ((d 0 3 + d 0 2) ^ q + (d 0 3 + d 0 1) ^ q - (d 0 1 + d 0 2) ^ q) / 2
    exact ((d 0 3 + d 0 2) ^ q + (d 0 3 + d 0 1) ^ q - |d 0 1 - d 0 2| ^ q) / 2
    · rw [hU, hV]
      gcongr
      · exact hnn _ _
      · exact hm.2.2.2 1 0 2 |> le_trans <| by linarith [hm.2.1 0 1, hm.2.1 0 2]
    · gcongr
      · exact hnn _ _
      · linarith
      · exact hnn _ _
      · linarith
      · have ha := hm.2.2.2 0 1 2
        have hb := hm.2.2.2 0 2 1
        cases abs_cases (d 0 1 - d 0 2) <;>
          linarith! [ha, hb, hm.2.1 0 1, hm.2.1 0 2, hm.2.1 1 2]
    · convert endpoint_star_det hq1 hq (d 0 3) (d 0 2) (d 0 1) (hnn _ _) (hnn _ _) (hnn _ _) using 1
      ring_nf
      unfold schoenDet
      ring_nf
      grind +qlia
    · convert endpoint_line_det hq0 hq2 (d 0 3) (d 0 1) (d 0 2) (hnn _ _) (hnn _ _) (hnn _ _) using 1
      unfold schoenDet
      ring_nf
      rw [hU, hV]
      ring
  have hdet : 0 ≤ schoenDet (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q)
      ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2)
      ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2)
      ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2) := by
    unfold schoenDet at h_det_nonneg ⊢
    rw [hU, hV] at h_det_nonneg ⊢
    ring_nf at h_det_nonneg ⊢
    positivity
  exact negType_of_schoenDet_nonneg hq0 hq2 d hm hdet

/-- Attached-ray negative type may be applied after relabelling the four points. -/
lemma attached_ray_negType_reindex {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) (σ : Equiv.Perm (Fin 4))
    (hU : d (σ 1) (σ 3) = d (σ 0) (σ 3) + d (σ 0) (σ 1))
    (hV : d (σ 2) (σ 3) = d (σ 0) (σ 3) + d (σ 0) (σ 2)) :
    HasNegType q d := by
  set E : Fin 4 → Fin 4 → ℝ := fun i j => d (σ i) (σ j)
  have hE : HasNegType q E :=
    attached_ray_negType hq1 hq E
      ⟨fun i => hm.1 _, fun i j => hm.2.1 _ _, fun i j => hm.2.2.1 _ _,
        fun i j k => hm.2.2.2 _ _ _⟩
      hU hV
  convert hasNegType_reindex σ⁻¹ hE using 1
  ext i j
  simp [E]

private lemma ptolemy_of_duplicate (u : Fin 4 → Fin 4 → ℝ)
    (hdiag : ∀ i, u i i = 0) (hsym : ∀ i j, u i j = u j i) (hnn : ∀ i j, 0 ≤ u i j)
    {x y z w : Fin 4}
    (hdup : x = y ∨ x = z ∨ x = w ∨ y = z ∨ y = w ∨ z = w) :
    u x y * u z w ≤ u x z * u y w + u x w * u y z := by
  rcases hdup with hxy | hxz | hxw | hyz | hyw | hzw
  · subst y
    rw [hdiag]
    nlinarith [mul_nonneg (hnn x z) (hnn x w)]
  · subst z
    rw [hdiag, hsym y x]
    nlinarith
  · subst w
    rw [hdiag, hsym z x, hsym y x]
    nlinarith
  · subst z
    rw [hdiag]
    nlinarith
  · subst w
    rw [hdiag, hsym z y]
    nlinarith
  · subst w
    rw [hdiag]
    nlinarith [mul_nonneg (hnn x z) (hnn y z)]

/-- Inversion of a four-point metric at the apex `3`. -/
noncomputable def apexInv (d : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j =>
    if i = j then 0
    else if i = 3 then 1 / d j 3
    else if j = 3 then 1 / d i 3
    else d i j / (d i 3 * d j 3)

private lemma apexInv_base_pos {d : Fin 4 → Fin 4 → ℝ}
    (h0 : 0 < d 0 3) (h1 : 0 < d 1 3) (h2 : 0 < d 2 3) :
    ∀ i : Fin 4, i ≠ 3 → 0 < d i 3 := by
  intro i hi
  fin_cases i <;> simp at hi
  · exact h0
  · exact h1
  · exact h2

private lemma apexInv_diag (d : Fin 4 → Fin 4 → ℝ) :
    ∀ i, apexInv d i i = 0 := by
  intro i
  simp [apexInv]

private lemma apexInv_symm {d : Fin 4 → Fin 4 → ℝ} (hsymm : ∀ i j, d i j = d j i) :
    ∀ i j, apexInv d i j = apexInv d j i := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [apexInv]
  · have hji : j ≠ i := Ne.symm hij
    by_cases hi3 : i = 3
    · subst i
      have hj3 : j ≠ 3 := hji
      simp [apexInv, hji, Ne.symm hj3]
    · by_cases hj3 : j = 3
      · subst j
        simp [apexInv, hij, Ne.symm hi3]
      · simp [apexInv, hij, hji, hi3, hj3, hsymm i j, mul_comm]

private lemma apexInv_nonneg {d : Fin 4 → Fin 4 → ℝ}
    (hnn : ∀ i j, 0 ≤ d i j)
    (hpos : ∀ i : Fin 4, i ≠ 3 → 0 < d i 3) :
    ∀ i j, 0 ≤ apexInv d i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [apexInv]
  · by_cases hi3 : i = 3
    · subst i
      have hj3 : j ≠ 3 := Ne.symm hij
      have hjpos := hpos j hj3
      simp [apexInv, hij, hjpos.le]
    · by_cases hj3 : j = 3
      · subst j
        have hipos := hpos i hi3
        simp [apexInv, hij, hipos.le]
      · have hden : 0 ≤ d i 3 * d j 3 := mul_nonneg (hpos i hi3).le (hpos j hj3).le
        simp [apexInv, hij, hi3, hj3, div_nonneg (hnn i j) hden]

private lemma apexInv_ptolemy_x_apex {d : Fin 4 → Fin 4 → ℝ} (hm : IsMetric4 d)
    (hpos : ∀ i : Fin 4, i ≠ 3 → 0 < d i 3)
    {y z w : Fin 4} (hy3 : y ≠ 3) (hz3 : z ≠ 3) (hw3 : w ≠ 3)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    apexInv d 3 y * apexInv d z w ≤
      apexInv d 3 z * apexInv d y w + apexInv d 3 w * apexInv d y z := by
  have hsymm := hm.2.1
  have htri := hm.2.2.2
  have hypos := hpos y hy3
  have hzpos := hpos z hz3
  have hwpos := hpos w hw3
  simp [apexInv, hy3, hz3, hw3, Ne.symm hy3, Ne.symm hz3, Ne.symm hw3,
    hyz, hyw, hzw]
  field_simp [hypos.ne', hzpos.ne', hwpos.ne']
  nlinarith [htri z y w, hsymm z y]

private lemma apexInv_ptolemy_y_apex {d : Fin 4 → Fin 4 → ℝ} (hm : IsMetric4 d)
    (hpos : ∀ i : Fin 4, i ≠ 3 → 0 < d i 3)
    {x z w : Fin 4} (hx3 : x ≠ 3) (hz3 : z ≠ 3) (hw3 : w ≠ 3)
    (hxz : x ≠ z) (hxw : x ≠ w) (hzw : z ≠ w) :
    apexInv d x 3 * apexInv d z w ≤
      apexInv d x z * apexInv d 3 w + apexInv d x w * apexInv d 3 z := by
  have hsymm := hm.2.1
  have htri := hm.2.2.2
  have hxpos := hpos x hx3
  have hzpos := hpos z hz3
  have hwpos := hpos w hw3
  simp [apexInv, hx3, hz3, hw3, Ne.symm hz3, Ne.symm hw3,
    hxz, hxw, hzw]
  field_simp [hxpos.ne', hzpos.ne', hwpos.ne']
  nlinarith [htri z x w, hsymm z x]

private lemma apexInv_ptolemy_z_apex {d : Fin 4 → Fin 4 → ℝ} (hm : IsMetric4 d)
    (hpos : ∀ i : Fin 4, i ≠ 3 → 0 < d i 3)
    {x y w : Fin 4} (hx3 : x ≠ 3) (hy3 : y ≠ 3) (hw3 : w ≠ 3)
    (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w) :
    apexInv d x y * apexInv d 3 w ≤
      apexInv d x 3 * apexInv d y w + apexInv d x w * apexInv d y 3 := by
  have hsymm := hm.2.1
  have htri := hm.2.2.2
  have hxpos := hpos x hx3
  have hypos := hpos y hy3
  have hwpos := hpos w hw3
  simp [apexInv, hx3, hy3, hw3, Ne.symm hw3,
    hxy, hxw, hyw]
  field_simp [hxpos.ne', hypos.ne', hwpos.ne']
  nlinarith [htri x w y, hsymm w y]

private lemma apexInv_ptolemy_w_apex {d : Fin 4 → Fin 4 → ℝ} (hm : IsMetric4 d)
    (hpos : ∀ i : Fin 4, i ≠ 3 → 0 < d i 3)
    {x y z : Fin 4} (hx3 : x ≠ 3) (hy3 : y ≠ 3) (hz3 : z ≠ 3)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    apexInv d x y * apexInv d z 3 ≤
      apexInv d x z * apexInv d y 3 + apexInv d x 3 * apexInv d y z := by
  have hsymm := hm.2.1
  have htri := hm.2.2.2
  have hxpos := hpos x hx3
  have hypos := hpos y hy3
  have hzpos := hpos z hz3
  simp [apexInv, hx3, hy3, hz3, hxy, hxz, hyz]
  field_simp [hxpos.ne', hypos.ne', hzpos.ne']
  nlinarith [htri x z y, hsymm z y]

/-- The metric inverted at the apex `3` is again a metric (uses Ptolemaicity of `d` for
the triangle inequality). -/
lemma inv_isMetric {d : Fin 4 → Fin 4 → ℝ} (hm : IsMetric4 d) (hp : IsPtolemaic4 d)
    (h0 : 0 < d 0 3) (h1 : 0 < d 1 3) (h2 : 0 < d 2 3) :
    IsMetric4 (apexInv d) := by
  set dh : Fin 4 → Fin 4 → ℝ := apexInv d
  have hpos : ∀ i : Fin 4, i ≠ 3 → 0 < d i 3 := apexInv_base_pos h0 h1 h2
  have hsymm := hm.2.1
  have htri := hm.2.2.2
  have hsymdh : ∀ i j, dh i j = dh j i := by
    simpa [dh] using apexInv_symm hsymm
  have hnonneg : ∀ i j, 0 ≤ dh i j := by
    simpa [dh] using apexInv_nonneg hm.2.2.1 hpos
  refine ⟨by simpa [dh] using apexInv_diag d, hsymdh, hnonneg, ?_⟩
  intro i j k
  by_cases hik : i = k
  · subst k
    simpa [dh, apexInv] using add_nonneg (hnonneg i j) (hnonneg j i)
  by_cases hij : i = j
  · subst j
    simp [dh, apexInv]
  by_cases hjk : j = k
  · subst k
    simp [dh, apexInv]
  by_cases hj3 : j = 3
  · subst j
    have hi3 : i ≠ 3 := by exact hij
    have hk3 : k ≠ 3 := by exact Ne.symm hjk
    have hipos := hpos i hi3
    have hkpos := hpos k hk3
    simp [dh, apexInv, hik, hi3, hk3, Ne.symm hk3]
    field_simp [hipos.ne', hkpos.ne']
    nlinarith [htri i 3 k, hsymm 3 k]
  by_cases hi3 : i = 3
  · subst i
    have hj3' : j ≠ 3 := hj3
    have hk3 : k ≠ 3 := by exact Ne.symm hik
    have hjpos := hpos j hj3'
    have hkpos := hpos k hk3
    simp [dh, apexInv, hik, hjk, hj3', hk3, Ne.symm hj3']
    field_simp [hjpos.ne', hkpos.ne']
    nlinarith [htri j k 3]
  by_cases hk3 : k = 3
  · subst k
    have hipos := hpos i hi3
    have hjpos := hpos j hj3
    simp [dh, apexInv, hik, hij, hj3]
    field_simp [hipos.ne', hjpos.ne']
    nlinarith [htri j i 3, hsymm j i]
  have hipos := hpos i hi3
  have hjpos := hpos j hj3
  have hkpos := hpos k hk3
  have hpt := hp i k j 3
  rw [hsymm k j] at hpt
  simp [dh, apexInv, hik, hij, hjk, hi3, hj3, hk3]
  field_simp [hipos.ne', hjpos.ne', hkpos.ne']
  nlinarith [hpt]

/-- The metric inverted at the apex `3` is Ptolemaic — its Ptolemy inequalities reduce
to the triangle inequalities of `d`. -/
lemma inv_isPtolemaic {d : Fin 4 → Fin 4 → ℝ} (hm : IsMetric4 d)
    (h0 : 0 < d 0 3) (h1 : 0 < d 1 3) (h2 : 0 < d 2 3) :
    IsPtolemaic4 (apexInv d) := by
  set dh : Fin 4 → Fin 4 → ℝ := apexInv d
  have hpos : ∀ i : Fin 4, i ≠ 3 → 0 < d i 3 := apexInv_base_pos h0 h1 h2
  have hdiag : ∀ i, dh i i = 0 := by
    simpa [dh] using apexInv_diag d
  have hsymdh : ∀ i j, dh i j = dh j i := by
    simpa [dh] using apexInv_symm hm.2.1
  have hnonneg : ∀ i j, 0 ≤ dh i j := by
    simpa [dh] using apexInv_nonneg hm.2.2.1 hpos
  intro x y z w
  by_cases hdup : x = y ∨ x = z ∨ x = w ∨ y = z ∨ y = w ∨ z = w
  · exact ptolemy_of_duplicate dh hdiag hsymdh hnonneg hdup
  push Not at hdup
  obtain ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ := hdup
  by_cases hx3 : x = 3
  · subst x
    simpa [dh] using apexInv_ptolemy_x_apex hm hpos
      (Ne.symm hxy) (Ne.symm hxz) (Ne.symm hxw) hyz hyw hzw
  by_cases hy3 : y = 3
  · subst y
    simpa [dh] using apexInv_ptolemy_y_apex hm hpos
      hxy (Ne.symm hyz) (Ne.symm hyw) hxz hxw hzw
  by_cases hz3 : z = 3
  · subst z
    simpa [dh] using apexInv_ptolemy_z_apex hm hpos
      hxz hyz (Ne.symm hzw) hxy hxw hyw
  by_cases hw3 : w = 3
  · subst w
    simpa [dh] using apexInv_ptolemy_w_apex hm hpos
      hxw hyw hzw hxy hxz hyz
  exfalso
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases w <;> simp at *

/-- **Reusable inversion bridge.**  If the metric inverted at the apex `3` has
`q`-negative type, then the base-`3` Schoenberg determinant of `d` is nonnegative.
(This is the metric-inversion / `schoenDet_congr` core of `geodesic_ptolemy_endpoint_det`,
extracted so that *any* proof of `HasNegType` for the inverted metric — e.g. via
`geodesic_insertion_negType` after a reindex — yields the determinant bound.) -/
lemma apex3_det_of_inversion {q : ℝ} (hq1 : 1 ≤ q)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) (hp : IsPtolemaic4 d)
    (hpos0 : 0 < d 0 3) (hpos1 : 0 < d 1 3) (hpos2 : 0 < d 2 3)
    (hdhneg : HasNegType q (apexInv d)) :
    0 ≤ schoenDet (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q)
        ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2)
        ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2)
        ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2) := by
  have hq0 : (0 : ℝ) < q := by linarith
  set dh : Fin 4 → Fin 4 → ℝ := apexInv d
  have hdh_metric : IsMetric4 dh := inv_isMetric hm hp hpos0 hpos1 hpos2
  have h_det_eq : schoenDet (dh 0 3 ^ q) (dh 1 3 ^ q) (dh 2 3 ^ q) ((dh 0 3 ^ q + dh 1 3 ^ q - dh 0 1 ^ q) / 2) ((dh 0 3 ^ q + dh 2 3 ^ q - dh 0 2 ^ q) / 2) ((dh 1 3 ^ q + dh 2 3 ^ q - dh 1 2 ^ q) / 2) = (d 0 3 ^ (-q) * d 1 3 ^ (-q) * d 2 3 ^ (-q)) ^ 2 * schoenDet (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q) ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2) ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2) ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2) := by
    convert schoenDet_congr (d 0 3 ^ (-q)) (d 1 3 ^ (-q)) (d 2 3 ^ (-q)) (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q) ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2) ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2) ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2) using 1
    simp +zetaDelta [apexInv]
    norm_num [Real.rpow_neg hpos0.le, Real.rpow_neg hpos1.le, Real.rpow_neg hpos2.le, Real.div_rpow (show 0 ≤ d 0 1 by exact hm.2.2.1 _ _) (show 0 ≤ d 0 3 * d 1 3 by positivity), Real.div_rpow (show 0 ≤ d 0 2 by exact hm.2.2.1 _ _) (show 0 ≤ d 0 3 * d 2 3 by positivity), Real.div_rpow (show 0 ≤ d 1 2 by exact hm.2.2.1 _ _) (show 0 ≤ d 1 3 * d 2 3 by positivity)]
    norm_num [Real.inv_rpow (le_of_lt hpos0), Real.inv_rpow (le_of_lt hpos1), Real.inv_rpow (le_of_lt hpos2), Real.mul_rpow (le_of_lt hpos0) (le_of_lt hpos1), Real.mul_rpow (le_of_lt hpos0) (le_of_lt hpos2), Real.mul_rpow (le_of_lt hpos1) (le_of_lt hpos2)]
    field_simp
    ring_nf
  contrapose! h_det_eq
  refine ne_of_gt (lt_of_lt_of_le ?_ (det_nonneg_of_negType (by positivity) dh ?_ ?_ hdhneg))
  · exact mul_neg_of_pos_of_neg (sq_pos_of_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hpos0 _) (Real.rpow_pos_of_pos hpos1 _)) (Real.rpow_pos_of_pos hpos2 _))) h_det_eq
  · exact hdh_metric.2.1
  · exact fun i => hdh_metric.1 i

/-
**Metric-inversion (Ptolemy-equality) endpoint.**  With apex `A = 3`, `P = 1`
on the geodesic `A`–`B = 2`, all apex distances positive, and the Ptolemy bound
holding with equality, the Schoenberg determinant based at `3` is nonnegative.
After inversion at the apex, the metric is an attached-ray configuration; the
shared inversion bridge transports that negative-type proof back to the original
Schoenberg determinant.
-/
lemma geodesic_ptolemy_endpoint_det {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) (hp : IsPtolemaic4 d)
    (hpos0 : 0 < d 0 3) (hpos1 : 0 < d 1 3) (hpos2 : 0 < d 2 3)
    (hgeo : d 3 2 = d 3 1 + d 1 2)
    (hPtEq : (d 3 1 + d 1 2) * d 0 1 = d 1 2 * d 0 3 + d 3 1 * d 0 2) :
    0 ≤ schoenDet (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q)
        ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2)
        ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2)
        ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2) := by
  set dh : Fin 4 → Fin 4 → ℝ := apexInv d
  have hdh_metric : IsMetric4 dh := inv_isMetric hm hp hpos0 hpos1 hpos2
  have hdh_negType : HasNegType q dh :=
    attached_ray_negType_reindex hq1 hq dh hdh_metric (Equiv.swap 0 2 * Equiv.swap 1 3)
      (by
        simp +decide [dh, apexInv, Equiv.swap_apply_def]
        field_simp [hpos1.ne', hpos2.ne']
        rw [hm.2.1 2 3, hm.2.1 2 1, hm.2.1 1 3]
        linarith [hgeo])
      (by
        simp +decide [dh, apexInv, Equiv.swap_apply_def]
        field_simp [hpos0.ne', hpos1.ne', hpos2.ne']
        rw [hm.2.1 2 3, hm.2.1 2 1, hm.2.1 2 0, hm.2.1 1 3]
        rw [hgeo]
        ring_nf at hPtEq ⊢
        exact Real.ext_cauchy (congrArg Real.cauchy hPtEq))
  exact apex3_det_of_inversion hq1 d hm hp hpos0 hpos1 hpos2 hdh_negType

/-- **Ptolemy-equality endpoint, apex-between labeling.** Here the apex `3` lies on the
geodesic between leaves `0` and `1`, and the Ptolemy inequality for `d 2 3` holds with
equality.  This is `geodesic_ptolemy_endpoint_det` under the relabelling `pm = (0 2 1 3)`,
which sends our "apex 3 between 0,1" to its "leaf 1 between apex 3 and leaf 2"; the
determinant is transported back through `negType` (which is base-independent). -/
lemma ptolemy_apex_endpoint_det {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) (hp : IsPtolemaic4 d)
    (hp02 : 0 < d 0 2) (hp03 : 0 < d 0 3) (hp13 : 0 < d 1 3)
    (hgeo : d 0 1 = d 0 3 + d 1 3)
    (hPtEq : d 2 3 * d 0 1 = d 0 2 * d 1 3 + d 0 3 * d 1 2) :
    0 ≤ schoenDet (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q)
        ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2)
        ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2)
        ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2) := by
  obtain ⟨hd, hsymm, hnn, htri⟩ := hm
  have hq0 : (0 : ℝ) < q := by linarith
  have hq2 : q ≤ 2 := le_two_of_le_logb23 hq
  have hd01 : 0 < d 0 1 := by rw [hgeo]; linarith
  -- The reindexed metric `E = d ∘ pm`, `pm = (0 2 1 3)`.
  set pm : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * (Equiv.swap 0 1 * Equiv.swap 0 2) with hpm
  set E : Fin 4 → Fin 4 → ℝ := fun i j => d (pm i) (pm j) with hE
  have hpm0 : pm 0 = 2 := by rw [hpm]; decide
  have hpm1 : pm 1 = 3 := by rw [hpm]; decide
  have hpm2 : pm 2 = 1 := by rw [hpm]; decide
  have hpm3 : pm 3 = 0 := by rw [hpm]; decide
  have hmE : IsMetric4 E :=
    ⟨fun i => hd _, fun i j => hsymm _ _, fun i j => hnn _ _, fun i j k => htri _ _ _⟩
  have hpE : IsPtolemaic4 E := fun x y z w => hp _ _ _ _
  -- `E` satisfies the hypotheses of `geodesic_ptolemy_endpoint_det`.
  have hgeoE : E 3 2 = E 3 1 + E 1 2 := by
    simp only [hE, hpm1, hpm2, hpm3]
    linarith [hgeo, hsymm 3 1]
  have hPtEqE : (E 3 1 + E 1 2) * E 0 1 = E 1 2 * E 0 3 + E 3 1 * E 0 2 := by
    simp only [hE, hpm0, hpm1, hpm2, hpm3]
    rw [hsymm 3 1, hsymm 2 0, hsymm 2 1]
    rw [hgeo] at hPtEq
    nlinarith [hPtEq]
  have hposE0 : 0 < E 0 3 := by simp only [hE, hpm0, hpm3]; rw [hsymm 2 0]; exact hp02
  have hposE1 : 0 < E 1 3 := by simp only [hE, hpm1, hpm3]; rw [hsymm 3 0]; exact hp03
  have hposE2 : 0 < E 2 3 := by simp only [hE, hpm2, hpm3]; rw [hsymm 1 0]; exact hd01
  have hdetE := geodesic_ptolemy_endpoint_det hq1 hq E hmE hpE hposE0 hposE1 hposE2 hgeoE hPtEqE
  -- Transport: `negType E`, reindex to `negType d`, then the base-3 determinant.
  have hnegE : HasNegType q E := negType_of_schoenDet_nonneg hq0 hq2 E hmE hdetE
  have hnegd : HasNegType q d := by
    convert hasNegType_reindex pm⁻¹ hnegE using 1
    exact funext fun i => funext fun j => by rw [hE]; rw [hpm]; congr 1 <;> simp [Equiv.Perm.mul_apply]
  exact det_nonneg_of_negType hq0 d hsymm hd hnegd

/-- Updating the `2`–`3` entry of a metric to a value `v` with `d23 ≤ v ≤ d20+d30` and
`v ≤ d21+d31` preserves metricity. -/
lemma isMetric4_update23 {d : Fin 4 → Fin 4 → ℝ}
    (hsymm : ∀ i j, d i j = d j i) (hnn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (v : ℝ) (hv0 : 0 ≤ v) (hvge : d 2 3 ≤ v)
    (hvle0 : v ≤ d 2 0 + d 3 0) (hvle1 : v ≤ d 2 1 + d 3 1) :
    IsMetric4 (fun i j => if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then v else d i j) := by
  set du : Fin 4 → Fin 4 → ℝ :=
    fun i j => if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then v else d i j
  have hge : ∀ i j, d i j ≤ du i j := by
    intro i j
    by_cases h : (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [du, hvge]
      · simp [du]
        linarith [hvge, hsymm 3 2]
    · simp [du, h]
  refine ⟨fun i => ?_, fun i j => ?_, fun i j => ?_, fun i j k => ?_⟩
  · fin_cases i <;> simp +decide [du, hd]
  · by_cases h : (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
    · simp only [du, if_pos h, if_pos (show (j = 2 ∧ i = 3) ∨ (j = 3 ∧ i = 2) by tauto)]
    · simp only [du, if_neg h, if_neg (show ¬((j = 2 ∧ i = 3) ∨ (j = 3 ∧ i = 2)) by tauto)]
      exact hsymm i j
  · fin_cases i <;> fin_cases j <;> simp +decide [du] <;> first | exact hnn _ _ | exact hv0
  · by_cases hik : (i = 2 ∧ k = 3) ∨ (i = 3 ∧ k = 2)
    · rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · fin_cases j <;> simp +decide [du, hd] <;> linarith [hvle0, hvle1, hsymm 3 0, hsymm 3 1]
      · fin_cases j <;> simp +decide [du, hd] <;>
          linarith [hvle0, hvle1, hsymm 2 0, hsymm 3 0, hsymm 2 1, hsymm 3 1]
    · calc
        du i k = d i k := by simp [du, hik]
        _ ≤ d i j + d j k := htri i j k
        _ ≤ du i j + du j k := add_le_add (hge i j) (hge j k)

/-- Updating the `2`–`3` entry of a metric to a smaller value `v`, subject to the
two remaining triangle intervals, preserves metricity. -/
lemma isMetric4_update23_lo {d : Fin 4 → Fin 4 → ℝ}
    (hsymm : ∀ i j, d i j = d j i) (hnn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (v : ℝ) (hv0 : 0 ≤ v)
    (hu0 : v ≤ d 2 0 + d 3 0) (hu1 : v ≤ d 2 1 + d 3 1)
    (hl0 : |d 2 0 - d 3 0| ≤ v) (hl1 : |d 2 1 - d 3 1| ≤ v) :
    IsMetric4 (fun i j => if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then v else d i j) := by
  obtain ⟨hl0a, hl0b⟩ := abs_le.mp hl0
  obtain ⟨hl1a, hl1b⟩ := abs_le.mp hl1
  refine ⟨fun i => ?_, fun i j => ?_, fun i j => ?_, fun i j k => ?_⟩
  · fin_cases i <;> simp +decide [hd]
  · by_cases h : (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
    · simp only [if_pos h, if_pos (show (j = 2 ∧ i = 3) ∨ (j = 3 ∧ i = 2) by tauto)]
    · simp only [if_neg h, if_neg (show ¬((j = 2 ∧ i = 3) ∨ (j = 3 ∧ i = 2)) by tauto)]
      exact hsymm i j
  · fin_cases i <;> fin_cases j <;> simp +decide <;> first | exact hnn _ _ | exact hv0
  · fin_cases i <;> fin_cases j <;> fin_cases k <;> simp +decide [hd] <;>
      first
      | exact htri _ _ _
      | linarith [hv0, hu0, hu1, hl0a, hl0b, hl1a, hl1b,
          hsymm 0 1, hsymm 0 2, hsymm 0 3, hsymm 1 2, hsymm 1 3, hsymm 2 3,
          htri 0 1 2, htri 0 2 1, htri 1 0 2, htri 1 2 0, htri 2 0 1, htri 2 1 0,
          htri 0 1 3, htri 0 3 1, htri 1 0 3, htri 1 3 0, htri 3 0 1, htri 3 1 0,
          htri 0 2 3, htri 0 3 2, htri 2 0 3, htri 2 3 0, htri 3 0 2, htri 3 2 0,
          htri 1 2 3, htri 1 3 2, htri 2 1 3, htri 2 3 1, htri 3 1 2, htri 3 2 1,
          hnn 0 1, hnn 0 2, hnn 0 3, hnn 1 2, hnn 1 3, hnn 2 3]

private lemma isPtolemaic4_update23_of_bounds {d : Fin 4 → Fin 4 → ℝ}
    (hsymm : ∀ i j, d i j = d j i) (hnn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (t : ℝ) (ht0 : 0 ≤ t)
    (hPup : t * d 0 1 ≤ d 0 2 * d 1 3 + d 0 3 * d 1 2)
    (k2 : d 0 2 * d 1 3 ≤ d 0 1 * t + d 0 3 * d 1 2)
    (k3 : d 0 3 * d 1 2 ≤ d 0 1 * t + d 0 2 * d 1 3) :
    IsPtolemaic4 (fun i j => if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then t else d i j) := by
  set du : Fin 4 → Fin 4 → ℝ :=
    fun i j => if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then t else d i j
  have hdiag : ∀ i, du i i = 0 := by
    intro i
    fin_cases i <;> simp [du, hd]
  have hsymdu : ∀ i j, du i j = du j i := by
    intro i j
    by_cases h : (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
    · simp only [du, if_pos h, if_pos (show (j = 2 ∧ i = 3) ∨ (j = 3 ∧ i = 2) by tauto)]
    · simp only [du, if_neg h, if_neg (show ¬((j = 2 ∧ i = 3) ∨ (j = 3 ∧ i = 2)) by tauto)]
      exact hsymm i j
  have hnndu : ∀ i j, 0 ≤ du i j := by
    intro i j
    by_cases h : (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
    · simp [du, h, ht0]
    · simp [du, h, hnn i j]
  intro x y z w
  by_cases hdup : x = y ∨ x = z ∨ x = w ∨ y = z ∨ y = w ∨ z = w
  · exact ptolemy_of_duplicate du hdiag hsymdu hnndu hdup
  push Not at hdup
  obtain ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ := hdup
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases w <;>
    simp [du] at hxy hxz hxw hyz hyw hzw ⊢ <;> try contradiction
  all_goals
    try simp only [hsymm 1 0, hsymm 2 0, hsymm 2 1, hsymm 3 0, hsymm 3 1]
    nlinarith [hPup, k2, k3]

/-- Updating the `2`–`3` entry of a Ptolemaic metric to a value below the upper Ptolemy
bound (`t * d01 ≤ d02*d13 + d03*d12`, with `t ≥ d23`) preserves Ptolemaicity. -/
lemma isPtolemaic4_update23 {d : Fin 4 → Fin 4 → ℝ} (hp : IsPtolemaic4 d)
    (hsymm : ∀ i j, d i j = d j i) (hnn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : d 2 3 ≤ t)
    (htP : t * d 0 1 ≤ d 0 2 * d 1 3 + d 0 3 * d 1 2) :
    IsPtolemaic4 (fun i j => if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then t else d i j) := by
  -- The three Ptolemy inequalities for the updated pair, in canonical form.
  have k2 : d 0 2 * d 1 3 ≤ d 0 1 * t + d 0 3 * d 1 2 := by
    have h := hp 0 2 1 3
    rw [hsymm 2 1] at h
    linarith [h, mul_le_mul_of_nonneg_left ht (hnn 0 1)]
  have k3 : d 0 3 * d 1 2 ≤ d 0 1 * t + d 0 2 * d 1 3 := by
    have h := hp 0 3 1 2
    rw [hsymm 3 2, hsymm 3 1] at h
    linarith [h, mul_le_mul_of_nonneg_left ht (hnn 0 1)]
  exact isPtolemaic4_update23_of_bounds hsymm hnn hd t ht0 htP k2 k3

/-- **Geodesic-insertion face** (`lem:q5-radial`): the apex `3` lies on the geodesic
between leaves `0` and `1` (`d 0 1 = d 0 3 + d 1 3`).  Since `schoenDet` is concave in
the apex distance `d 2 3` (`schoenDet_concave_apex`), reduce `d 2 3` over its feasible
interval (triangle + Ptolemy bounds) keeping `d01, d02, d12` fixed; each endpoint is a
valid Ptolemaic configuration (line / attached-ray / Ptolemy-equality). -/
lemma geodesic_insertion_det {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) (hp : IsPtolemaic4 d)
    (hp03 : 0 < d 0 3) (hp13 : 0 < d 1 3) (hgeo : d 0 1 = d 0 3 + d 1 3) :
    0 ≤ schoenDet (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q)
        ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2)
        ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2)
        ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2) := by
  obtain ⟨hd, hsymm, hnn, htri⟩ := hm
  have hq0 : (0 : ℝ) < q := by linarith
  have hd01 : 0 < d 0 1 := by rw [hgeo]; linarith
  set L := max |d 0 3 - d 0 2| (max |d 1 3 - d 1 2| (|d 0 2 * d 1 3 - d 0 3 * d 1 2| / d 0 1))
    with hLdef
  set U := min (d 0 3 + d 0 2) (min (d 1 3 + d 1 2) ((d 0 2 * d 1 3 + d 0 3 * d 1 2) / d 0 1))
    with hUdef
  have hLnn : 0 ≤ L := le_max_of_le_left (abs_nonneg _)
  have hLd : L ≤ d 2 3 := by
    rw [hLdef]
    refine max_le ?_ (max_le ?_ ?_)
    · rw [abs_le]
      exact ⟨by linarith [htri 0 3 2, hsymm 3 2], by linarith [htri 0 2 3]⟩
    · rw [abs_le]
      exact ⟨by linarith [htri 1 3 2, hsymm 3 2], by linarith [htri 1 2 3]⟩
    · rw [div_le_iff₀ hd01, abs_le]
      have ha := hp 0 2 1 3
      rw [hsymm 2 1] at ha
      have hb := hp 0 3 1 2
      rw [hsymm 3 2, hsymm 3 1] at hb
      exact ⟨by nlinarith [ha], by nlinarith [hb]⟩
  have hdU : d 2 3 ≤ U := by
    rw [hUdef]
    refine le_min ?_ (le_min ?_ ?_)
    · linarith [htri 2 0 3, hsymm 2 0]
    · linarith [htri 2 1 3, hsymm 2 1]
    · rw [le_div_iff₀ hd01]
      have hc := hp 2 3 0 1
      rw [hsymm 2 0, hsymm 3 1, hsymm 2 1, hsymm 3 0] at hc
      nlinarith [hc]
  refine schoenDet_concave_apex (d 0 3 ^ q) (d 1 3 ^ q) (d 0 2 ^ q) (d 1 2 ^ q)
    ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2)
    (by have := Real.rpow_nonneg (hnn 0 1) q; linarith)
    (d 2 3 ^ q) (L ^ q) (U ^ q)
    (Real.rpow_le_rpow hLnn hLd hq0.le)
    (Real.rpow_le_rpow (hLnn.trans hLd) hdU hq0.le) ?_ ?_
  · -- lower endpoint `d 2 3 = L`: a triangle or Ptolemy bound is tight.
    have hq2 : q ≤ 2 := le_two_of_le_logb23 hq
    rw [hLdef]
    rcases max_cases |d 0 3 - d 0 2| (max |d 1 3 - d 1 2| (|d 0 2 * d 1 3 - d 0 3 * d 1 2| / d 0 1))
      with ⟨hLeq, hLge⟩ | ⟨hLeq, hLlt⟩
    · -- `L = |d03 - d02|`, with the Ptolemy-lo bound `≤ |d03-d02|`.
      rw [hLeq]
      have hPt : |d 0 2 * d 1 3 - d 0 3 * d 1 2| ≤ |d 0 3 - d 0 2| * d 0 1 := by
        rw [← div_le_iff₀ hd01]
        exact le_trans (le_max_right _ _) hLge
      rcases le_total (d 0 2) (d 0 3) with hcmp | hcmp
      · -- `d03 ≥ d02`: `2` between `0,3`; Ptolemy forces `d12 = d01 - d02`, line `0,2,3,1`.
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ d 0 3 - d 0 2)] at hPt ⊢
        have hd12 : d 1 2 = d 0 1 - d 0 2 := by
          have hge : d 0 1 - d 0 2 ≤ d 1 2 := by linarith [htri 0 2 1, hsymm 2 1]
          have hPt' : d 0 3 * d 1 2 - d 0 2 * d 1 3 ≤ (d 0 3 - d 0 2) * d 0 1 := by
            have h1 := le_abs_self (d 0 3 * d 1 2 - d 0 2 * d 1 3)
            rw [abs_sub_comm] at h1
            linarith [h1, hPt]
          have hmul : d 0 3 * d 1 2 ≤ d 0 3 * (d 0 1 - d 0 2) := by rw [hgeo] at hPt'; nlinarith [hPt']
          have := le_of_mul_le_mul_left hmul hp03
          linarith
        rw [hd12, hgeo]
        set x : Fin 4 → ℝ := fun i =>
          if i = 0 then 0 else if i = 1 then d 0 3 + d 1 3 else if i = 2 then d 0 2 else d 0 3
          with hxdef
        have hx0 : x 0 = 0 := by simp [hxdef]
        have hx1 : x 1 = d 0 3 + d 1 3 := by simp [hxdef]
        have hx2 : x 2 = d 0 2 := by simp [hxdef]
        have hx3 : x 3 = d 0 3 := by simp [hxdef]
        have e01 : |x 0 - x 1| = d 0 3 + d 1 3 := by
          rw [hx0, hx1, abs_of_nonpos (by linarith [hnn 0 3, hnn 1 3])]
          ring
        have e02 : |x 0 - x 2| = d 0 2 := by
          rw [hx0, hx2, abs_of_nonpos (by linarith [hnn 0 2])]
          ring
        have e03 : |x 0 - x 3| = d 0 3 := by
          rw [hx0, hx3, abs_of_nonpos (by linarith [hnn 0 3])]
          ring
        have e12 : |x 1 - x 2| = d 0 3 + d 1 3 - d 0 2 := by
          rw [hx1, hx2, abs_of_nonneg (by linarith)]
        have e13 : |x 1 - x 3| = d 1 3 := by
          rw [hx1, hx3, abs_of_nonneg (by linarith [hnn 1 3])]
          ring
        have e23 : |x 2 - x 3| = d 0 3 - d 0 2 := by
          rw [hx2, hx3, abs_of_nonpos (by linarith)]
          ring
        have key := line_schoenDet_nonneg hq0 hq2 x
        simp only [e01, e02, e03, e12, e13, e23] at key
        exact key
      · -- `d02 ≥ d03`: `3` between `0,2`; attached-ray (apex `0`, junction `3`, leaves `1,2`).
        have hLval : |d 0 3 - d 0 2| = d 0 2 - d 0 3 := by rw [abs_of_nonpos (by linarith)]; ring
        rw [hLval]
        have hLge' : |d 1 3 - d 1 2| ≤ d 0 2 - d 0 3 := by
          have h := le_trans (le_max_left _ _) hLge
          rwa [hLval] at h
        obtain ⟨hge1, hge2⟩ := abs_le.mp hLge'
        set dA : Fin 4 → Fin 4 → ℝ :=
          fun i j => if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then d 0 2 - d 0 3 else d i j with hdA
        have hmA : IsMetric4 dA := by
          rw [hdA]
          apply isMetric4_update23_lo hsymm hnn hd htri
          · linarith
          · rw [hsymm 2 0, hsymm 3 0]
            linarith [hnn 0 3]
          · rw [hsymm 2 1, hsymm 3 1]
            linarith [hgeo, htri 0 1 2]
          · rw [hsymm 2 0, hsymm 3 0, abs_of_nonneg (by linarith : 0 ≤ d 0 2 - d 0 3)]
          · rwa [hsymm 2 1, hsymm 3 1, abs_sub_comm]
        have hneg : HasNegType q dA :=
          attached_ray_negType_reindex hq1 hq dA hmA (Equiv.swap 0 3)
            (by simp +decide [hdA, Equiv.swap_apply_def]
                linarith [hgeo, hsymm 1 0, hsymm 3 1, hsymm 3 0])
            (by simp +decide [hdA, Equiv.swap_apply_def]
                linarith [hsymm 2 0, hsymm 3 0])
        have hdet := det_nonneg_of_negType hq0 dA hmA.2.1 hmA.1 hneg
        convert hdet using 3 <;> simp [hdA]
    · -- `L = max |d13-d12| (Ptolemy-lo)`
      rw [hLeq]
      rcases max_cases |d 1 3 - d 1 2| (|d 0 2 * d 1 3 - d 0 3 * d 1 2| / d 0 1)
        with ⟨hL2eq, hL2ge⟩ | ⟨hL2eq, hL2lt⟩
      · -- `L = |d13 - d12|`, with Ptolemy-lo `≤ |d13-d12|`.
        rw [hL2eq]
        have hPt : |d 0 2 * d 1 3 - d 0 3 * d 1 2| ≤ |d 1 3 - d 1 2| * d 0 1 := by
          rw [← div_le_iff₀ hd01]
          exact hL2ge
        rcases le_total (d 1 2) (d 1 3) with hcmp | hcmp
        · -- `d13 ≥ d12`: `2` between `1,3`; Ptolemy forces `d02 = d01 - d12`, line `0,3,2,1`.
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ d 1 3 - d 1 2)] at hPt ⊢
          have hd02 : d 0 2 = d 0 1 - d 1 2 := by
            have hge : d 0 1 - d 1 2 ≤ d 0 2 := by linarith [htri 0 2 1, hsymm 2 1]
            have hPt' : d 0 2 * d 1 3 - d 0 3 * d 1 2 ≤ (d 1 3 - d 1 2) * d 0 1 :=
              le_trans (le_abs_self _) hPt
            have hmul : d 1 3 * d 0 2 ≤ d 1 3 * (d 0 1 - d 1 2) := by rw [hgeo] at hPt'; nlinarith [hPt']
            have := le_of_mul_le_mul_left hmul hp13
            linarith
          rw [hd02, hgeo]
          set x : Fin 4 → ℝ := fun i =>
            if i = 0 then 0 else if i = 1 then d 0 3 + d 1 3 else if i = 2 then d 0 3 + d 1 3 - d 1 2 else d 0 3
            with hxdef
          have hx0 : x 0 = 0 := by simp [hxdef]
          have hx1 : x 1 = d 0 3 + d 1 3 := by simp [hxdef]
          have hx2 : x 2 = d 0 3 + d 1 3 - d 1 2 := by simp [hxdef]
          have hx3 : x 3 = d 0 3 := by simp [hxdef]
          have e01 : |x 0 - x 1| = d 0 3 + d 1 3 := by
            rw [hx0, hx1, abs_of_nonpos (by linarith [hnn 0 3, hnn 1 3])]
            ring
          have e02 : |x 0 - x 2| = d 0 3 + d 1 3 - d 1 2 := by
            rw [hx0, hx2, abs_of_nonpos (by linarith [hnn 0 2])]
            ring
          have e03 : |x 0 - x 3| = d 0 3 := by
            rw [hx0, hx3, abs_of_nonpos (by linarith [hnn 0 3])]
            ring
          have e12 : |x 1 - x 2| = d 1 2 := by
            rw [hx1, hx2, abs_of_nonneg (by linarith [hnn 1 2])]
            ring
          have e13 : |x 1 - x 3| = d 1 3 := by
            rw [hx1, hx3, abs_of_nonneg (by linarith [hnn 1 3])]
            ring
          have e23 : |x 2 - x 3| = d 1 3 - d 1 2 := by
            rw [hx2, hx3, abs_of_nonneg (by linarith)]
            ring
          have key := line_schoenDet_nonneg hq0 hq2 x
          simp only [e01, e02, e03, e12, e13, e23] at key
          exact key
        · -- `d12 ≥ d13`: `3` between `1,2`; attached-ray (apex `1`, junction `3`, leaves `0,2`).
          have hLval : |d 1 3 - d 1 2| = d 1 2 - d 1 3 := by rw [abs_of_nonpos (by linarith)]; ring
          rw [hLval]
          have hb02 : d 0 2 - d 0 3 ≤ d 1 2 - d 1 3 := by
            have h1 : |d 0 3 - d 0 2| < |d 1 3 - d 1 2| := by rw [hL2eq] at hLlt; exact hLlt
            have h2 : d 0 2 - d 0 3 ≤ |d 0 3 - d 0 2| := by rw [abs_sub_comm]; exact le_abs_self _
            rw [hLval] at h1
            linarith [h1, h2]
          set dA : Fin 4 → Fin 4 → ℝ :=
            fun i j => if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then d 1 2 - d 1 3 else d i j with hdA
          have hmA : IsMetric4 dA := by
            rw [hdA]
            apply isMetric4_update23_lo hsymm hnn hd htri
            · linarith
            · rw [hsymm 2 0, hsymm 3 0]
              linarith [hgeo, htri 1 0 2, hsymm 1 0]
            · rw [hsymm 2 1, hsymm 3 1]
              linarith [hnn 1 3]
            · rw [hsymm 2 0, hsymm 3 0, abs_sub_comm]
              rw [← hLval]
              exact le_of_lt (by rw [hL2eq] at hLlt; exact hLlt)
            · rw [hsymm 2 1, hsymm 3 1, abs_of_nonneg (by linarith : 0 ≤ d 1 2 - d 1 3)]
          have hneg : HasNegType q dA :=
            attached_ray_negType_reindex hq1 hq dA hmA (Equiv.swap 0 1 * Equiv.swap 0 3)
              (by simp +decide [hdA, Equiv.swap_apply_def]
                  linarith [hgeo, hsymm 1 0, hsymm 3 1, hsymm 3 0])
              (by simp +decide [hdA, Equiv.swap_apply_def]
                  linarith [hsymm 2 1, hsymm 3 1])
          have hdet := det_nonneg_of_negType hq0 dA hmA.2.1 hmA.1 hneg
          convert hdet using 3 <;> simp [hdA]
      · -- `L = Ptolemy-lo`: this branch is vacuous.  The Ptolemy lower bound never
        -- strictly exceeds *both* triangle bounds, since
        -- `d02·d13 - d03·d12 = -(d03-d02)·d13 + (d13-d12)·d03`, so
        -- `|d02·d13 - d03·d12| ≤ max |d03-d02| |d13-d12| · d01`.
        exfalso
        rw [hL2eq] at hLlt
        have hkey : |d 0 2 * d 1 3 - d 0 3 * d 1 2|
            ≤ |d 0 3 - d 0 2| * d 1 3 + |d 1 3 - d 1 2| * d 0 3 := by
          rw [abs_le, abs_sub_comm (d 0 3) (d 0 2)]
          constructor <;>
            nlinarith [le_abs_self (d 0 2 - d 0 3), neg_abs_le (d 0 2 - d 0 3),
              le_abs_self (d 1 3 - d 1 2), neg_abs_le (d 1 3 - d 1 2), hnn 0 3, hnn 1 3,
              mul_nonneg (abs_nonneg (d 0 2 - d 0 3)) (hnn 1 3),
              mul_nonneg (abs_nonneg (d 1 3 - d 1 2)) (hnn 0 3)]
        have hPle : |d 0 2 * d 1 3 - d 0 3 * d 1 2| / d 0 1
            ≤ max |d 0 3 - d 0 2| |d 1 3 - d 1 2| := by
          rw [div_le_iff₀ hd01, hgeo]
          have ha := le_max_left |d 0 3 - d 0 2| |d 1 3 - d 1 2|
          have hb := le_max_right |d 0 3 - d 0 2| |d 1 3 - d 1 2|
          nlinarith [hkey, mul_le_mul_of_nonneg_right ha hp13.le,
            mul_le_mul_of_nonneg_right hb hp03.le]
        linarith [max_lt hLlt hL2lt, hPle]
  · -- upper endpoint `d 2 3 = U`: a triangle or Ptolemy bound is tight.
    have hq2 : q ≤ 2 := le_two_of_le_logb23 hq
    rw [hUdef]
    rcases min_cases (d 0 3 + d 0 2) (min (d 1 3 + d 1 2) ((d 0 2 * d 1 3 + d 0 3 * d 1 2) / d 0 1))
      with ⟨hUeq, hUle⟩ | ⟨hUeq, hUlt1⟩
    · -- `U = d03 + d02`: Ptolemy forces `d12 = d01 + d02`, giving the line `2,0,3,1`.
      rw [hUeq]
      have hPt : (d 0 3 + d 0 2) * d 0 1 ≤ d 0 2 * d 1 3 + d 0 3 * d 1 2 := by
        have h := le_trans hUle (min_le_right _ _)
        rwa [le_div_iff₀ hd01] at h
      have hd12 : d 1 2 = d 0 1 + d 0 2 := by
        have h012 : d 1 2 ≤ d 0 1 + d 0 2 := by linarith [htri 1 0 2, hsymm 1 0]
        have hmul : d 0 3 * (d 0 1 + d 0 2) ≤ d 0 3 * d 1 2 := by rw [hgeo] at hPt; nlinarith [hPt]
        have := le_of_mul_le_mul_left hmul hp03
        linarith
      rw [hd12, hgeo]
      set x : Fin 4 → ℝ := fun i =>
        if i = 0 then 0 else if i = 1 then d 0 3 + d 1 3 else if i = 2 then -d 0 2 else d 0 3
        with hxdef
      have hx0 : x 0 = 0 := by simp [hxdef]
      have hx1 : x 1 = d 0 3 + d 1 3 := by simp [hxdef]
      have hx2 : x 2 = -d 0 2 := by simp [hxdef]
      have hx3 : x 3 = d 0 3 := by simp [hxdef]
      have e01 : |x 0 - x 1| = d 0 3 + d 1 3 := by
        rw [hx0, hx1, abs_of_nonpos (by linarith [hnn 0 3, hnn 1 3])]
        ring
      have e02 : |x 0 - x 2| = d 0 2 := by
        rw [hx0, hx2, abs_of_nonneg (by linarith [hnn 0 2])]
        ring
      have e03 : |x 0 - x 3| = d 0 3 := by
        rw [hx0, hx3, abs_of_nonpos (by linarith [hnn 0 3])]
        ring
      have e12 : |x 1 - x 2| = d 0 3 + d 1 3 + d 0 2 := by
        rw [hx1, hx2, abs_of_nonneg (by linarith [hnn 0 3, hnn 1 3, hnn 0 2])]
        ring
      have e13 : |x 1 - x 3| = d 1 3 := by
        rw [hx1, hx3, abs_of_nonneg (by linarith [hnn 1 3])]
        ring
      have e23 : |x 2 - x 3| = d 0 3 + d 0 2 := by
        rw [hx2, hx3, abs_of_nonpos (by linarith [hnn 0 3, hnn 0 2])]
        ring
      have key := line_schoenDet_nonneg hq0 hq2 x
      simp only [e01, e02, e03, e12, e13, e23] at key
      exact key
    · -- `U = min (d13+d12) (Ptolemy-hi)`
      rw [hUeq]
      rcases min_cases (d 1 3 + d 1 2) ((d 0 2 * d 1 3 + d 0 3 * d 1 2) / d 0 1)
        with ⟨hUeq2, hUle2⟩ | ⟨hUeq2, hUlt2⟩
      · -- `U = d13 + d12`: Ptolemy forces `d02 = d01 + d12`, giving the line `2,1,3,0`.
        rw [hUeq2]
        have hPt : (d 1 3 + d 1 2) * d 0 1 ≤ d 0 2 * d 1 3 + d 0 3 * d 1 2 := by
          rwa [le_div_iff₀ hd01] at hUle2
        have hd02 : d 0 2 = d 0 1 + d 1 2 := by
          have h021 : d 0 2 ≤ d 0 1 + d 1 2 := by linarith [htri 0 1 2]
          have hmul : d 1 3 * (d 0 1 + d 1 2) ≤ d 1 3 * d 0 2 := by rw [hgeo] at hPt; nlinarith [hPt]
          have := le_of_mul_le_mul_left hmul hp13
          linarith
        rw [hd02, hgeo]
        set x : Fin 4 → ℝ := fun i =>
          if i = 0 then d 1 2 + d 1 3 + d 0 3 else if i = 1 then d 1 2 else if i = 2 then 0 else d 1 2 + d 1 3
          with hxdef
        have hx0 : x 0 = d 1 2 + d 1 3 + d 0 3 := by simp [hxdef]
        have hx1 : x 1 = d 1 2 := by simp [hxdef]
        have hx2 : x 2 = 0 := by simp [hxdef]
        have hx3 : x 3 = d 1 2 + d 1 3 := by simp [hxdef]
        have e01 : |x 0 - x 1| = d 0 3 + d 1 3 := by
          rw [hx0, hx1, abs_of_nonneg (by linarith [hnn 0 3, hnn 1 3])]
          ring
        have e02 : |x 0 - x 2| = d 0 3 + d 1 3 + d 1 2 := by
          rw [hx0, hx2, abs_of_nonneg (by linarith [hnn 0 3, hnn 1 3, hnn 1 2])]
          ring
        have e03 : |x 0 - x 3| = d 0 3 := by
          rw [hx0, hx3, abs_of_nonneg (by linarith [hnn 0 3])]
          ring
        have e12 : |x 1 - x 2| = d 1 2 := by
          rw [hx1, hx2, abs_of_nonneg (by linarith [hnn 1 2])]
          ring
        have e13 : |x 1 - x 3| = d 1 3 := by
          rw [hx1, hx3, abs_of_nonpos (by linarith [hnn 1 3])]
          ring
        have e23 : |x 2 - x 3| = d 1 3 + d 1 2 := by
          rw [hx2, hx3, abs_of_nonpos (by linarith [hnn 1 3, hnn 1 2])]
          ring
        have key := line_schoenDet_nonneg hq0 hq2 x
        simp only [e01, e02, e03, e12, e13, e23] at key
        exact key
      · -- `U = Ptolemy-hi`: Ptolemy equality ⇒ `ptolemy_apex_endpoint_det`.
        rw [hUeq2]
        rcases eq_or_lt_of_le (hnn 0 2) with hd02 | hd02
        · -- `d 0 2 = 0`: points `0` and `2` coincide, the apex value collapses to `d 0 3`,
          -- and the determinant is identically `0`.
          have h12 : d 1 2 = d 0 1 := by
            have h1 : d 1 2 ≤ d 0 1 := by linarith [htri 1 0 2, hsymm 1 0, hd02]
            have h2 : d 0 1 ≤ d 1 2 := by linarith [htri 1 2 0, hsymm 1 0, hsymm 2 0, hd02]
            linarith
          have hval : (d 0 2 * d 1 3 + d 0 3 * d 1 2) / d 0 1 = d 0 3 := by
            rw [← hd02, h12, zero_mul, zero_add, mul_div_assoc, div_self hd01.ne', mul_one]
          rw [hval, ← hd02, Real.zero_rpow hq0.ne', h12]
          apply le_of_eq
          unfold schoenDet
          ring
        · set t := (d 0 2 * d 1 3 + d 0 3 * d 1 2) / d 0 1 with ht
          have htval : t * d 0 1 = d 0 2 * d 1 3 + d 0 3 * d 1 2 := by rw [ht]; field_simp
          have htge : d 2 3 ≤ t := by
            rw [ht, le_div_iff₀ hd01]
            have hh := hp 2 3 0 1
            rw [hsymm 2 0, hsymm 3 1, hsymm 2 1, hsymm 3 0] at hh
            nlinarith [hh]
          have ht0 : 0 ≤ t := le_trans (hnn 2 3) htge
          have hb0 : t < d 0 3 + d 0 2 := by rw [hUeq2] at hUlt1; exact hUlt1
          have hb1 : t < d 1 3 + d 1 2 := hUlt2
          set dP : Fin 4 → Fin 4 → ℝ :=
            fun i j => if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then t else d i j with hdP
          have hmP : IsMetric4 dP := by
            rw [hdP]
            apply isMetric4_update23 hsymm hnn hd htri
            · exact ht0
            · exact htge
            · rw [hsymm 2 0, hsymm 3 0]
              linarith [hb0]
            · rw [hsymm 2 1, hsymm 3 1]
              linarith [hb1]
          have hpP : IsPtolemaic4 dP := isPtolemaic4_update23 hp hsymm hnn hd t ht0 htge (le_of_eq htval)
          have hkey := ptolemy_apex_endpoint_det hq1 hq dP hmP hpP
            (by simp [hdP]; exact hd02) (by simp [hdP]; exact hp03) (by simp [hdP]; exact hp13)
            (by simp [hdP]; exact hgeo) (by simp [hdP]; exact htval)
          convert hkey using 2 <;> simp [hdP]

/-- The `HasNegType` form of `geodesic_insertion_det`: the same geodesic-insertion
hypotheses give that `d` has `q`-negative type (the Schoenberg matrix based at `3` is
positive semidefinite — its determinant is `geodesic_insertion_det`, its `2×2` minors
are `minor_nonneg`).  Since `HasNegType` is permutation-invariant, the main proof can
reach a geodesic-insertion endpoint in *any* leaf labelling by reindexing. -/
lemma geodesic_insertion_negType {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) (hp : IsPtolemaic4 d)
    (hp03 : 0 < d 0 3) (hp13 : 0 < d 1 3) (hgeo : d 0 1 = d 0 3 + d 1 3) :
    HasNegType q d := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hq2 : q ≤ 2 := le_two_of_le_logb23 hq
  exact negType_of_schoenDet_nonneg hq0 hq2 d hm
    (geodesic_insertion_det hq1 hq d hm hp hp03 hp13 hgeo)

/-- Geodesic insertion may be applied after relabelling the four points. -/
lemma geodesic_insertion_negType_reindex {q : ℝ} (hq1 : 1 ≤ q)
    (hq : q ≤ Real.logb 2 3) (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d)
    (hp : IsPtolemaic4 d) (σ : Equiv.Perm (Fin 4))
    (hp03 : 0 < d (σ 0) (σ 3)) (hp13 : 0 < d (σ 1) (σ 3))
    (hgeo : d (σ 0) (σ 1) = d (σ 0) (σ 3) + d (σ 1) (σ 3)) :
    HasNegType q d := by
  set E : Fin 4 → Fin 4 → ℝ := fun i j => d (σ i) (σ j)
  have hE : HasNegType q E :=
    geodesic_insertion_negType hq1 hq E
      ⟨fun i => hm.1 _, fun i j => hm.2.1 _ _, fun i j => hm.2.2.1 _ _,
        fun i j k => hm.2.2.2 _ _ _⟩
      (fun x y z w => hp _ _ _ _) hp03 hp13 hgeo
  convert hasNegType_reindex σ⁻¹ hE using 1
  ext i j
  simp [E]

/-- Updating the `0`–`1` entry of a metric to a value `v` with `d01 ≤ v ≤ d02+d12` and
`v ≤ d03+d13` preserves metricity. -/
lemma isMetric4_update01 {d : Fin 4 → Fin 4 → ℝ}
    (hsymm : ∀ i j, d i j = d j i) (hnn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (v : ℝ) (hv0 : 0 ≤ v) (hvge : d 0 1 ≤ v)
    (hvle2 : v ≤ d 0 2 + d 1 2) (hvle3 : v ≤ d 0 3 + d 1 3) :
    IsMetric4 (fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then v else d i j) := by
  set du : Fin 4 → Fin 4 → ℝ :=
    fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then v else d i j
  have hge : ∀ i j, d i j ≤ du i j := by
    intro i j
    by_cases h : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [du, hvge]
      · simp [du]
        linarith [hvge, hsymm 1 0]
    · simp [du, h]
  refine ⟨fun i => ?_, fun i j => ?_, fun i j => ?_, fun i j k => ?_⟩
  · fin_cases i <;> simp +decide [du, hd]
  · by_cases h : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
    · simp only [du, if_pos h, if_pos (show (j = 0 ∧ i = 1) ∨ (j = 1 ∧ i = 0) by tauto)]
    · simp only [du, if_neg h, if_neg (show ¬((j = 0 ∧ i = 1) ∨ (j = 1 ∧ i = 0)) by tauto)]
      exact hsymm i j
  · fin_cases i <;> fin_cases j <;> simp +decide [du] <;> first | exact hnn _ _ | exact hv0
  · by_cases hik : (i = 0 ∧ k = 1) ∨ (i = 1 ∧ k = 0)
    · rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · fin_cases j <;> simp +decide [du, hd] <;> linarith [hvle2, hvle3, hsymm 2 1, hsymm 3 1]
      · fin_cases j <;> simp +decide [du, hd] <;>
          linarith [hvle2, hvle3, hsymm 2 0, hsymm 3 0]
    · calc
        du i k = d i k := by simp [du, hik]
        _ ≤ d i j + d j k := htri i j k
        _ ≤ du i j + du j k := add_le_add (hge i j) (hge j k)

private lemma isPtolemaic4_update01_of_bounds {d : Fin 4 → Fin 4 → ℝ}
    (hsymm : ∀ i j, d i j = d j i) (hnn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (v : ℝ) (hv0 : 0 ≤ v)
    (hPup : v * d 2 3 ≤ d 0 2 * d 1 3 + d 0 3 * d 1 2)
    (k2 : d 0 2 * d 1 3 ≤ v * d 2 3 + d 0 3 * d 1 2)
    (k3 : d 0 3 * d 1 2 ≤ v * d 2 3 + d 0 2 * d 1 3) :
    IsPtolemaic4 (fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then v else d i j) := by
  set du : Fin 4 → Fin 4 → ℝ :=
    fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then v else d i j
  have hdiag : ∀ i, du i i = 0 := by
    intro i
    fin_cases i <;> simp [du, hd]
  have hsymdu : ∀ i j, du i j = du j i := by
    intro i j
    by_cases h : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
    · simp only [du, if_pos h, if_pos (show (j = 0 ∧ i = 1) ∨ (j = 1 ∧ i = 0) by tauto)]
    · simp only [du, if_neg h, if_neg (show ¬((j = 0 ∧ i = 1) ∨ (j = 1 ∧ i = 0)) by tauto)]
      exact hsymm i j
  have hnndu : ∀ i j, 0 ≤ du i j := by
    intro i j
    by_cases h : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
    · simp [du, h, hv0]
    · simp [du, h, hnn i j]
  intro x y z w
  by_cases hdup : x = y ∨ x = z ∨ x = w ∨ y = z ∨ y = w ∨ z = w
  · exact ptolemy_of_duplicate du hdiag hsymdu hnndu hdup
  push Not at hdup
  obtain ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ := hdup
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases w <;>
    simp [du] at hxy hxz hxw hyz hyw hzw ⊢ <;> try contradiction
  all_goals
    try simp only [hsymm 2 0, hsymm 3 0, hsymm 2 1, hsymm 3 1, hsymm 3 2]
    nlinarith [hPup, k2, k3]

/-- Updating the `0`–`1` entry of a Ptolemaic metric to `v` (with `d01 ≤ v` and the
Ptolemy upper bound `v·d23 ≤ d02·d13 + d03·d12`) preserves Ptolemaicity. -/
lemma isPtolemaic4_update01 {d : Fin 4 → Fin 4 → ℝ} (hp : IsPtolemaic4 d)
    (hsymm : ∀ i j, d i j = d j i) (hnn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (v : ℝ) (hv0 : 0 ≤ v) (hvge : d 0 1 ≤ v)
    (hvP : v * d 2 3 ≤ d 0 2 * d 1 3 + d 0 3 * d 1 2) :
    IsPtolemaic4 (fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then v else d i j) := by
  -- The three Ptolemy inequalities for the updated pair, in canonical form.
  have k2 : d 0 2 * d 1 3 ≤ v * d 2 3 + d 0 3 * d 1 2 := by
    have h := hp 0 2 1 3
    rw [hsymm 2 1] at h
    linarith [h, mul_le_mul_of_nonneg_right hvge (hnn 2 3)]
  have k3 : d 0 3 * d 1 2 ≤ v * d 2 3 + d 0 2 * d 1 3 := by
    have h := hp 0 3 1 2
    rw [hsymm 3 2, hsymm 3 1] at h
    linarith [h, mul_le_mul_of_nonneg_right hvge (hnn 2 3)]
  exact isPtolemaic4_update01_of_bounds hsymm hnn hd v hv0 hvP k2 k3

/-- Updating the `0`–`1` entry of a metric to a *smaller* value `v` (with the triangle
bounds `|d02-d12| ≤ v ≤ d02+d12` and `|d03-d13| ≤ v ≤ d03+d13`) preserves metricity. -/
lemma isMetric4_update01_lo {d : Fin 4 → Fin 4 → ℝ}
    (hsymm : ∀ i j, d i j = d j i) (hnn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (v : ℝ) (hv0 : 0 ≤ v)
    (hu2 : v ≤ d 0 2 + d 1 2) (hu3 : v ≤ d 0 3 + d 1 3)
    (hl2 : |d 0 2 - d 1 2| ≤ v) (hl3 : |d 0 3 - d 1 3| ≤ v) :
    IsMetric4 (fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then v else d i j) := by
  obtain ⟨hl2a, hl2b⟩ := abs_le.mp hl2
  obtain ⟨hl3a, hl3b⟩ := abs_le.mp hl3
  refine ⟨fun i => ?_, fun i j => ?_, fun i j => ?_, fun i j k => ?_⟩
  · fin_cases i <;> simp +decide [hd]
  · by_cases h : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
    · simp only [if_pos h, if_pos (show (j = 0 ∧ i = 1) ∨ (j = 1 ∧ i = 0) by tauto)]
    · simp only [if_neg h, if_neg (show ¬((j = 0 ∧ i = 1) ∨ (j = 1 ∧ i = 0)) by tauto)]
      exact hsymm i j
  · fin_cases i <;> fin_cases j <;> simp +decide <;> first | exact hnn _ _ | exact hv0
  · fin_cases i <;> fin_cases j <;> fin_cases k <;> simp +decide [hd] <;>
      first
      | exact htri _ _ _
      | linarith [hv0, hu2, hu3, hl2a, hl2b, hl3a, hl3b,
          hsymm 0 1, hsymm 0 2, hsymm 0 3, hsymm 1 2, hsymm 1 3, hsymm 2 3,
          htri 0 1 2, htri 0 2 1, htri 1 0 2, htri 1 2 0, htri 2 0 1, htri 2 1 0,
          htri 0 1 3, htri 0 3 1, htri 1 0 3, htri 1 3 0, htri 3 0 1, htri 3 1 0,
          htri 0 2 3, htri 0 3 2, htri 2 0 3, htri 2 3 0, htri 3 0 2, htri 3 2 0,
          htri 1 2 3, htri 1 3 2, htri 2 1 3, htri 2 3 1, htri 3 1 2, htri 3 2 1,
          hnn 0 1, hnn 0 2, hnn 0 3, hnn 1 2, hnn 1 3, hnn 2 3]

/-- Updating the `0`–`1` entry of a Ptolemaic metric to a *smaller* value `v`, with the
upper Ptolemy bound `v·d23 ≤ d02·d13+d03·d12` and the lower one
`|d02·d13 - d03·d12| ≤ v·d23`, preserves Ptolemaicity. -/
lemma isPtolemaic4_update01_lo {d : Fin 4 → Fin 4 → ℝ} (_hp : IsPtolemaic4 d)
    (hsymm : ∀ i j, d i j = d j i) (hnn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (v : ℝ) (hv0 : 0 ≤ v)
    (hPup : v * d 2 3 ≤ d 0 2 * d 1 3 + d 0 3 * d 1 2)
    (hPlo : |d 0 2 * d 1 3 - d 0 3 * d 1 2| ≤ v * d 2 3) :
    IsPtolemaic4 (fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then v else d i j) := by
  obtain ⟨hlo1, hlo2⟩ := abs_le.mp hPlo
  -- The three Ptolemy inequalities for the updated pair, in canonical form.
  have k2 : d 0 2 * d 1 3 ≤ v * d 2 3 + d 0 3 * d 1 2 := by linarith
  have k3 : d 0 3 * d 1 2 ≤ v * d 2 3 + d 0 2 * d 1 3 := by linarith
  exact isPtolemaic4_update01_of_bounds hsymm hnn hd v hv0 hPup k2 k3

/-- **The hard core: nonnegativity of the Schoenberg determinant.**
For a four-point Ptolemaic metric and `1 ≤ q ≤ log₂ 3`, the determinant of the
`3×3` Schoenberg matrix based at point `3` is nonnegative.

This is the heart of `thm:q5-four-point-ptolemaic`.  The intended proof is the
case analysis of the paper: fixing the leaf lengths `ρᵢ = d i 3`, the determinant
`schoenDet` is a concave quadratic in each off-diagonal entry (`schoenDet_ge_of_endpoints`),
so it is `≥ 0` once it is `≥ 0` at the endpoints of each feasible interval.  Every
such endpoint is a geodesic-insertion configuration (`lem:q5-radial`), which in turn
reduces — via the one-entry concavity, the attached-ray lemma
(`attached_ray_negType`), the line and star metrics (`line_negType`, `star_negType`),
and the metric-inversion diagonal congruence (`schoenDet_congr`) — to the cases
already established above.  All supporting lemmas are proved; only this final
combinatorial assembly (the geodesic-insertion lemma and the polytope case
analysis) remains. -/
lemma schoenberg_det_nonneg {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) (hp : IsPtolemaic4 d) :
    0 ≤ d 0 3 ^ q * d 1 3 ^ q * d 2 3 ^ q
        + 2 * ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2)
            * ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2)
            * ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2)
        - d 0 3 ^ q * ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2) ^ 2
        - d 1 3 ^ q * ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2) ^ 2
        - d 2 3 ^ q * ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2) ^ 2 := by
  obtain ⟨hd, hsymm, hnn, htri⟩ := hm
  have hq0 : (0 : ℝ) < q := by linarith
  -- Degenerate cases: if any apex distance vanishes, the apex coincides (metrically)
  -- with that leaf, the corresponding off-diagonal entries collapse, and the
  -- determinant is identically `0`.
  by_cases hA : d 0 3 = 0
  · have e01 : d 0 1 = d 1 3 :=
      le_antisymm (by linarith [htri 0 3 1, hsymm 3 1, hA]) (by linarith [htri 1 0 3, hsymm 1 0, hA])
    have e02 : d 0 2 = d 2 3 :=
      le_antisymm (by linarith [htri 0 3 2, hsymm 3 2, hA]) (by linarith [htri 2 0 3, hsymm 2 0, hA])
    rw [hA, e01, e02, Real.zero_rpow hq0.ne']
    nlinarith
  by_cases hB : d 1 3 = 0
  · have e01 : d 0 1 = d 0 3 :=
      le_antisymm (by linarith [htri 0 3 1, hsymm 3 1, hB]) (by linarith [htri 0 1 3, hB])
    have e12 : d 1 2 = d 2 3 :=
      le_antisymm (by linarith [htri 1 3 2, hsymm 3 2, hB]) (by linarith [htri 2 1 3, hsymm 2 1, hB])
    rw [hB, e01, e12, Real.zero_rpow hq0.ne']
    nlinarith
  by_cases hC : d 2 3 = 0
  · have e02 : d 0 2 = d 0 3 :=
      le_antisymm (by linarith [htri 0 3 2, hsymm 3 2, hC]) (by linarith [htri 0 2 3, hC])
    have e12 : d 1 2 = d 1 3 :=
      le_antisymm (by linarith [htri 1 3 2, hsymm 3 2, hC]) (by linarith [htri 1 2 3, hC])
    rw [hC, e02, e12, Real.zero_rpow hq0.ne']
    nlinarith
  by_cases hP : d 0 2 = 0
  · have e03 : d 2 3 = d 0 3 :=
      le_antisymm (by linarith [htri 2 0 3, hsymm 2 0, hP]) (by linarith [htri 0 2 3, hP])
    have e12 : d 1 2 = d 0 1 :=
      le_antisymm (by linarith [htri 1 0 2, hsymm 1 0, hP]) (by linarith [htri 0 2 1, hsymm 2 1, hP])
    rw [hP, e03, e12, Real.zero_rpow hq0.ne']
    nlinarith
  by_cases hQ : d 1 2 = 0
  · have e13 : d 2 3 = d 1 3 :=
      le_antisymm (by linarith [htri 2 1 3, hsymm 2 1, hQ]) (by linarith [htri 1 2 3, hQ])
    have e02 : d 0 2 = d 0 1 :=
      le_antisymm (by linarith [htri 0 1 2, hQ]) (by linarith [htri 0 2 1, hsymm 2 1, hQ])
    rw [hQ, e13, e02, Real.zero_rpow hq0.ne']
    nlinarith
  by_cases hR : d 0 1 = 0
  · have e13 : d 0 3 = d 1 3 :=
      le_antisymm (by linarith [htri 0 1 3, hR]) (by linarith [htri 1 0 3, hsymm 1 0, hR])
    have e02 : d 0 2 = d 1 2 :=
      le_antisymm (by linarith [htri 0 1 2, hR]) (by linarith [htri 1 0 2, hsymm 1 0, hR])
    rw [hR, e13, e02, Real.zero_rpow hq0.ne']
    nlinarith
  -- Main case: all six pairwise distances are strictly positive.
  have hA' : 0 < d 0 3 := lt_of_le_of_ne (hnn 0 3) (Ne.symm hA)
  have hB' : 0 < d 1 3 := lt_of_le_of_ne (hnn 1 3) (Ne.symm hB)
  have hC' : 0 < d 2 3 := lt_of_le_of_ne (hnn 2 3) (Ne.symm hC)
  have hP' : 0 < d 0 2 := lt_of_le_of_ne (hnn 0 2) (Ne.symm hP)
  have hQ' : 0 < d 1 2 := lt_of_le_of_ne (hnn 1 2) (Ne.symm hQ)
  have hR' : 0 < d 0 1 := lt_of_le_of_ne (hnn 0 1) (Ne.symm hR)
  -- Fold the goal into canonical `schoenDet` form, ready for the concavity
  -- reduction (`schoenDet_ge_of_endpoints`) and leaf-permutation lemmas.
  suffices h : 0 ≤ schoenDet (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q)
      ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2)
      ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2)
      ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2) by
    simpa [schoenDet] using h
  -- Reduce the leaves-{0,1} entry by varying `d 0 1` over its feasible interval.
  -- The interval endpoints are the tightest of the triangle bounds (`{0,1,3}`,
  -- `{0,1,2}`) and the Ptolemy bound; at each endpoint a constraint is tight, giving
  -- a geodesic-insertion or Ptolemy-equality configuration.
  apply schoenDet_reduce_dist hq0 (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q)
      ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2)
      ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2)
      (Real.rpow_nonneg hC'.le _)
      (d 0 1)
      (max (max |d 0 3 - d 1 3| |d 0 2 - d 1 2|) (|d 0 2 * d 1 3 - d 0 3 * d 1 2| / d 2 3))
      (min (min (d 0 3 + d 1 3) (d 0 2 + d 1 2)) ((d 0 2 * d 1 3 + d 0 3 * d 1 2) / d 2 3))
  · -- `0 ≤ t1`
    exact le_max_of_le_left (le_max_of_le_left (abs_nonneg _))
  · -- `t1 ≤ d 0 1` : every lower bound is `≤ d 0 1`
    refine max_le (max_le ?_ ?_) ?_
    · rw [abs_le]
      exact ⟨by linarith [htri 1 0 3, hsymm 1 0], by linarith [htri 0 1 3]⟩
    · rw [abs_le]
      exact ⟨by linarith [htri 1 0 2, hsymm 1 0], by linarith [htri 0 1 2]⟩
    · rw [div_le_iff₀ hC', abs_le]
      have ha := hp 0 3 1 2
      rw [hsymm 3 2, hsymm 3 1] at ha
      have hb := hp 0 2 1 3
      rw [hsymm 2 1] at hb
      exact ⟨by linarith [ha], by linarith [hb]⟩
  · -- `d 0 1 ≤ t2` : `d 0 1` is below every upper bound
    refine le_min (le_min ?_ ?_) ?_
    · linarith [htri 0 3 1, hsymm 3 1]
    · linarith [htri 0 2 1, hsymm 2 1]
    · rw [le_div_iff₀ hC']
      linarith [hp 0 1 2 3]
  · -- endpoint `t1` (lower): the tightest lower bound is active.
    rcases max_cases (max |d 0 3 - d 1 3| |d 0 2 - d 1 2|) (|d 0 2 * d 1 3 - d 0 3 * d 1 2| / d 2 3)
      with ⟨he, hbo⟩ | ⟨he, hbo2⟩
    · rw [he]
      rcases max_cases |d 0 3 - d 1 3| |d 0 2 - d 1 2| with ⟨he2, hb⟩ | ⟨he2, hb⟩
      · rw [he2]
        -- `d 0 1 = |d03 - d13|`: collinear in the {0,1,3} triangle.
        have hPlo : |d 0 2 * d 1 3 - d 0 3 * d 1 2| ≤ |d 0 3 - d 1 3| * d 2 3 := by
          rw [← div_le_iff₀ hC']
          exact he2 ▸ hbo
        by_cases hz : d 0 3 = d 1 3
        · -- boundary `|d03-d13| = 0`: forces `d02 = d12`, determinant `≡ 0`.
          have hd02 : d 0 2 = d 1 2 := by
            have h0 : |d 0 2 - d 1 2| ≤ 0 := by have := hb; rwa [hz, sub_self, abs_zero] at this
            exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)
          rw [hz, hd02, sub_self, abs_zero, Real.zero_rpow hq0.ne']
          apply le_of_eq
          unfold schoenDet
          ring
        · have hvpos : 0 < |d 0 3 - d 1 3| := abs_pos.mpr (sub_ne_zero.mpr hz)
          have hvle01 : |d 0 3 - d 1 3| ≤ d 0 1 := by
            rw [abs_le]
            exact ⟨by linarith [htri 1 0 3, hsymm 1 0], by linarith [htri 0 1 3]⟩
          set d' : Fin 4 → Fin 4 → ℝ :=
            fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then |d 0 3 - d 1 3| else d i j with hd'
          have hm' : IsMetric4 d' := isMetric4_update01_lo hsymm hnn hd htri |d 0 3 - d 1 3|
            (abs_nonneg _)
            (by rw [abs_le]; exact ⟨by linarith [htri 1 0 3, hsymm 1 0, htri 0 2 1, hsymm 2 1],
              by linarith [htri 0 1 3, htri 0 2 1, hsymm 2 1]⟩)
            (by rw [abs_le]; exact ⟨by linarith [hnn 0 3, hnn 1 3], by linarith [hnn 0 3, hnn 1 3]⟩)
            hb le_rfl
          have hp' : IsPtolemaic4 d' := isPtolemaic4_update01_lo hp hsymm hnn hd |d 0 3 - d 1 3|
            (abs_nonneg _)
            (by nlinarith [mul_le_mul_of_nonneg_right hvle01 (hnn 2 3), hp 0 1 2 3])
            hPlo
          have hd'neg : HasNegType q d' := by
            rcases lt_or_gt_of_ne hz with hcmp | hcmp
            · -- `d03 < d13`: reindex by `(0 3)`
              exact geodesic_insertion_negType_reindex hq1 hq d' hm' hp' (Equiv.swap 0 3)
                (by simp +decide [hd']; linarith [hA', hsymm 3 0])
                (by positivity)
                (by simp +decide [hd', Equiv.swap_apply_def]
                    rw [abs_of_neg (by linarith : d 0 3 - d 1 3 < 0)]
                    linarith [hsymm 3 0, hsymm 3 1])
            · -- `d03 > d13`: reindex by `(1 3)`
              exact geodesic_insertion_negType_reindex hq1 hq d' hm' hp' (Equiv.swap 1 3)
                (by positivity)
                (by simp +decide [hd']; linarith [hB', hsymm 3 1])
                (by simp +decide [hd', Equiv.swap_apply_def]
                    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ d 0 3 - d 1 3)]
                    linarith [hsymm 3 1])
          have hdet := det_nonneg_of_negType hq0 d' hm'.2.1 hm'.1 hd'neg
          convert hdet using 2 <;> simp [hd']
      · rw [he2]
        -- `d 0 1 = |d02 - d12|`: collinear in the {0,1,2} triangle; here `|d02-d12| > 0`.
        have hvpos : 0 < |d 0 2 - d 1 2| := lt_of_le_of_lt (abs_nonneg _) hb
        have hne : d 0 2 ≠ d 1 2 := sub_ne_zero.mp (abs_pos.mp hvpos)
        have hPlo : |d 0 2 * d 1 3 - d 0 3 * d 1 2| ≤ |d 0 2 - d 1 2| * d 2 3 := by
          rw [← div_le_iff₀ hC']
          exact he2 ▸ hbo
        have hvle01 : |d 0 2 - d 1 2| ≤ d 0 1 := by
          rw [abs_le]
          exact ⟨by linarith [htri 1 0 2, hsymm 1 0], by linarith [htri 0 1 2]⟩
        set d' : Fin 4 → Fin 4 → ℝ :=
          fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then |d 0 2 - d 1 2| else d i j with hd'
        have hm' : IsMetric4 d' := isMetric4_update01_lo hsymm hnn hd htri |d 0 2 - d 1 2|
          (abs_nonneg _)
          (by rw [abs_le]; exact ⟨by linarith [hnn 0 2, hnn 1 2], by linarith [hnn 0 2, hnn 1 2]⟩)
          (by rw [abs_le]; exact ⟨by linarith [htri 1 0 2, hsymm 1 0, htri 0 3 1, hsymm 3 1],
            by linarith [htri 0 1 2, htri 0 3 1, hsymm 3 1]⟩)
          le_rfl (le_of_lt hb)
        have hp' : IsPtolemaic4 d' := isPtolemaic4_update01_lo hp hsymm hnn hd |d 0 2 - d 1 2|
          (abs_nonneg _)
          (by nlinarith [mul_le_mul_of_nonneg_right hvle01 (hnn 2 3), hp 0 1 2 3])
          hPlo
        have hd'neg : HasNegType q d' := by
          rcases lt_or_gt_of_ne hne with hcmp | hcmp
          · -- `d02 < d12`: reindex by `(0 2 3)`
            exact geodesic_insertion_negType_reindex hq1 hq d' hm' hp'
              (Equiv.swap 0 3 * Equiv.swap 0 2)
              (by simp +decide [hd', Equiv.swap_apply_def]; linarith [hP', hsymm 2 0])
              (by positivity)
              (by simp +decide [hd', Equiv.swap_apply_def]
                  rw [abs_of_neg (by linarith : d 0 2 - d 1 2 < 0)]
                  linarith [hsymm 2 0, hsymm 2 1])
          · -- `d02 > d12`: reindex by `(1 2 3)`
            exact geodesic_insertion_negType_reindex hq1 hq d' hm' hp'
              (Equiv.swap 1 3 * Equiv.swap 1 2)
              (by positivity)
              (by simp +decide [hd', Equiv.swap_apply_def]; linarith [hQ', hsymm 2 1])
              (by simp +decide [hd', Equiv.swap_apply_def]
                  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ d 0 2 - d 1 2)]
                  linarith [hsymm 2 1])
        have hdet := det_nonneg_of_negType hq0 d' hm'.2.1 hm'.1 hd'neg
        convert hdet using 2 <;> simp [hd']
    · rw [he]
      -- `d 0 1` at the lower Ptolemy bound.  Update `d01` to this value, then invert at the
      -- apex `3`: the inverted metric has a leaf between two others (which leaf depends on the
      -- sign of `d02·d13 - d03·d12`), so `apex3_det_of_inversion` applies.
      set v : ℝ := |d 0 2 * d 1 3 - d 0 3 * d 1 2| / d 2 3 with hv
      have hvpos : 0 < v := lt_of_le_of_lt (le_trans (abs_nonneg _) (le_max_left _ _)) hbo2
      have hPlo : |d 0 2 * d 1 3 - d 0 3 * d 1 2| ≤ v * d 2 3 :=
        le_of_eq (by rw [hv, div_mul_cancel₀ _ hC'.ne'])
      have hPup : v * d 2 3 ≤ d 0 2 * d 1 3 + d 0 3 * d 1 2 := by
        rw [hv, div_mul_cancel₀ _ hC'.ne']
        rcases abs_cases (d 0 2 * d 1 3 - d 0 3 * d 1 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
          nlinarith [mul_nonneg (hnn 0 2) (hnn 1 3), mul_nonneg (hnn 0 3) (hnn 1 2)]
      have hvd01 : v ≤ d 0 1 := by
        rw [hv, div_le_iff₀ hC']
        rcases abs_cases (d 0 2 * d 1 3 - d 0 3 * d 1 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
          nlinarith [hp 0 2 1 3, hp 0 3 1 2, hsymm 2 1, hsymm 3 2, hsymm 3 1]
      have hl2 : |d 0 2 - d 1 2| ≤ v := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hbo2)
      have hl3 : |d 0 3 - d 1 3| ≤ v := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hbo2)
      have hu2 : v ≤ d 0 2 + d 1 2 := le_trans hvd01 (by linarith [htri 0 2 1, hsymm 2 1])
      have hu3 : v ≤ d 0 3 + d 1 3 := le_trans hvd01 (by linarith [htri 0 3 1, hsymm 3 1])
      clear_value v
      set d' : Fin 4 → Fin 4 → ℝ :=
        fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then v else d i j with hd'
      have hm' : IsMetric4 d' := isMetric4_update01_lo hsymm hnn hd htri v hvpos.le hu2 hu3 hl2 hl3
      have hp' : IsPtolemaic4 d' := isPtolemaic4_update01_lo hp hsymm hnn hd v hvpos.le hPup hPlo
      have hpos0' : 0 < d' 0 3 := by positivity
      have hpos1' : 0 < d' 1 3 := by positivity
      have hpos2' : 0 < d' 2 3 := by positivity
      set D : Fin 4 → Fin 4 → ℝ := apexInv d' with hD
      have hDm : IsMetric4 D := inv_isMetric hm' hp' hpos0' hpos1' hpos2'
      have hDp : IsPtolemaic4 D := inv_isPtolemaic hm' hpos0' hpos1' hpos2'
      have hDneg : HasNegType q D := by
        rcases le_total (d 0 3 * d 1 2) (d 0 2 * d 1 3) with hsgn | hsgn
        · -- `d02·d13 ≥ d03·d12`: inverted `1'` between `0'`,`2'`; reindex by `(1 2 3)`
          exact geodesic_insertion_negType_reindex hq1 hq D hDm hDp
            (Equiv.swap 1 3 * Equiv.swap 1 2)
            (by simp +decide [hD, apexInv, hd', Equiv.swap_apply_def]; positivity)
            (by simp +decide [hD, apexInv, hd', Equiv.swap_apply_def, hsymm 2 1]; positivity)
            (by simp +decide [hD, apexInv, hd', Equiv.swap_apply_def, hv, hsymm 2 1]
                rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ d 0 2 * d 1 3 - d 0 3 * d 1 2)]
                field_simp
                ring)
        · -- `d03·d12 ≥ d02·d13`: inverted `0'` between `1'`,`2'`; reindex by `(0 2 3)`
          exact geodesic_insertion_negType_reindex hq1 hq D hDm hDp
            (Equiv.swap 0 3 * Equiv.swap 0 2)
            (by simp +decide [hD, apexInv, hd', Equiv.swap_apply_def, hsymm 2 0]; positivity)
            (by simp +decide [hD, apexInv, hd', Equiv.swap_apply_def]; positivity)
            (by simp +decide [hD, apexInv, hd', Equiv.swap_apply_def, hv, hsymm 2 1, hsymm 2 0]
                rw [abs_of_nonpos (by linarith : d 0 2 * d 1 3 - d 0 3 * d 1 2 ≤ 0)]
                field_simp
                ring)
      have hfinal := apex3_det_of_inversion hq1 d' hm' hp' hpos0' hpos1' hpos2' hDneg
      convert hfinal using 2 <;> simp [hd']
  · -- endpoint `t2` (upper): the tightest upper bound is active.
    rcases min_cases (min (d 0 3 + d 1 3) (d 0 2 + d 1 2)) ((d 0 2 * d 1 3 + d 0 3 * d 1 2) / d 2 3)
      with ⟨he, hble⟩ | ⟨he, hbe⟩
    · rw [he]
      rcases min_cases (d 0 3 + d 1 3) (d 0 2 + d 1 2) with ⟨he2, hb2⟩ | ⟨he2, hb2⟩
      · rw [he2]
        -- `d 0 1 = d03 + d13`: apex 3 lies between leaves 0 and 1 (geodesic insertion).
        have hvP : (d 0 3 + d 1 3) * d 2 3 ≤ d 0 2 * d 1 3 + d 0 3 * d 1 2 :=
          (le_div_iff₀ hC').mp (he2 ▸ hble)
        set d' : Fin 4 → Fin 4 → ℝ :=
          fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then d 0 3 + d 1 3 else d i j with hd'
        have hm' : IsMetric4 d' := isMetric4_update01 hsymm hnn hd htri (d 0 3 + d 1 3)
          (by positivity) (by linarith [htri 0 3 1, hsymm 3 1]) hb2 le_rfl
        have hp' : IsPtolemaic4 d' := isPtolemaic4_update01 hp hsymm hnn hd (d 0 3 + d 1 3)
          (add_nonneg (hnn 0 3) (hnn 1 3)) (by linarith [htri 0 3 1, hsymm 3 1]) hvP
        have hneg := geodesic_insertion_negType hq1 hq d' hm' hp'
          (by simp [hd']; exact hA') (by simp [hd']; exact hB') (by simp [hd'])
        have hdet := det_nonneg_of_negType hq0 d' hm'.2.1 hm'.1 hneg
        convert hdet using 2 <;> simp [hd']
      · rw [he2]
        -- `d 0 1 = d02 + d12`: leaf 2 lies between leaves 0 and 1.  Reindexing by the
        -- transposition `(2 3)` turns this into apex-`3`-between-`0`,`1`, so
        -- `geodesic_insertion_negType` applies; transport back by permutation invariance.
        have hvP : (d 0 2 + d 1 2) * d 2 3 ≤ d 0 2 * d 1 3 + d 0 3 * d 1 2 :=
          (le_div_iff₀ hC').mp (he2 ▸ hble)
        set d' : Fin 4 → Fin 4 → ℝ :=
          fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then d 0 2 + d 1 2 else d i j with hd'
        have hm' : IsMetric4 d' := isMetric4_update01 hsymm hnn hd htri (d 0 2 + d 1 2)
          (by positivity) (by linarith [htri 0 2 1, hsymm 2 1]) le_rfl
          (le_of_lt hb2)
        have hp' : IsPtolemaic4 d' := isPtolemaic4_update01 hp hsymm hnn hd (d 0 2 + d 1 2)
          (by positivity) (by linarith [htri 0 2 1, hsymm 2 1]) hvP
        have hd'neg : HasNegType q d' :=
          geodesic_insertion_negType_reindex hq1 hq d' hm' hp' (Equiv.swap 2 3)
            (by positivity)
            (by positivity)
            (by simp [hd', Equiv.swap_apply_def])
        have hdet := det_nonneg_of_negType hq0 d' hm'.2.1 hm'.1 hd'neg
        convert hdet using 2 <;> simp [hd']
    · rw [he]
      -- `d 0 1` at the upper Ptolemy bound: Ptolemy equality.  Update `d01` to this value,
      -- then invert at the apex `3`: the inverted metric has `2'` between `0'` and `1'`, a
      -- geodesic-insertion configuration, so `apex3_det_of_inversion` applies.
      have hvge : d 0 1 ≤ (d 0 2 * d 1 3 + d 0 3 * d 1 2) / d 2 3 :=
        (le_div_iff₀ hC').mpr (hp 0 1 2 3)
      have hvP : (d 0 2 * d 1 3 + d 0 3 * d 1 2) / d 2 3 * d 2 3 ≤ d 0 2 * d 1 3 + d 0 3 * d 1 2 :=
        le_of_eq (div_mul_cancel₀ _ hC'.ne')
      set d' : Fin 4 → Fin 4 → ℝ :=
        fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then (d 0 2 * d 1 3 + d 0 3 * d 1 2) / d 2 3
          else d i j with hd'
      have hm' : IsMetric4 d' := isMetric4_update01 hsymm hnn hd htri _
        (by positivity) hvge (le_of_lt (lt_of_lt_of_le hbe (min_le_right _ _)))
        (le_of_lt (lt_of_lt_of_le hbe (min_le_left _ _)))
      have hp' : IsPtolemaic4 d' := isPtolemaic4_update01 hp hsymm hnn hd _
        (by positivity) hvge hvP
      have hpos0' : 0 < d' 0 3 := by simp [hd']; exact hA'
      have hpos1' : 0 < d' 1 3 := by simp [hd']; exact hB'
      have hpos2' : 0 < d' 2 3 := by simp [hd']; exact hC'
      set D : Fin 4 → Fin 4 → ℝ := apexInv d' with hD
      have hDm : IsMetric4 D := inv_isMetric hm' hp' hpos0' hpos1' hpos2'
      have hDp : IsPtolemaic4 D := inv_isPtolemaic hm' hpos0' hpos1' hpos2'
      have hd'01 : d' 0 1 = (d 0 2 * d 1 3 + d 0 3 * d 1 2) / d 2 3 := by simp [hd']
      have hDneg : HasNegType q D :=
        geodesic_insertion_negType_reindex hq1 hq D hDm hDp (Equiv.swap 2 3)
          (by simp +decide [hD, apexInv, hd', Equiv.swap_apply_def]; positivity)
          (by simp +decide [hD, apexInv, hd', Equiv.swap_apply_def]; positivity)
          (by simp +decide [hD, apexInv, hd', Equiv.swap_apply_def]; field_simp)
      have hfinal := apex3_det_of_inversion hq1 d' hm' hp' hpos0' hpos1' hpos2' hDneg
      convert hfinal using 2 <;> simp [hd']

/-
**Negative type for `1 ≤ q ≤ log₂ 3`** via the positive semidefinite Schoenberg
matrix.
-/
lemma negType_ge_one {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) (hp : IsPtolemaic4 d) :
    HasNegType q d := by
  exact negType_of_schoenDet_nonneg (by linarith) (le_two_of_le_logb23 hq)
    d hm (schoenberg_det_nonneg hq1 hq d hm hp)

/-- Determinant decomposition when `g01` is the smallest Gromov product. -/
private lemma det_gromov_nonneg_of_g01_min (r0 r1 r2 g01 g02 g12 : ℝ)
    (hg01 : 0 ≤ g01) (h0102 : g01 ≤ g02) (h0112 : g01 ≤ g12)
    (h02 : g02 ≤ r0) (h12 : g12 ≤ r1) (t2 : g02 + g12 - g01 ≤ r2) :
    0 ≤ r0 * r1 * r2 + 2 * g01 * g02 * g12 - r0 * g12 ^ 2 - r1 * g02 ^ 2
      - r2 * g01 ^ 2 := by
  have hA : 0 ≤ r0 - g02 := by linarith
  have hB : 0 ≤ r1 - g12 := by linarith
  have hC : 0 ≤ r2 - (g02 + g12 - g01) := by linarith
  have hD : 0 ≤ g02 - g01 := by linarith
  have hE : 0 ≤ g12 - g01 := by linarith
  have hdecomp :
      r0 * r1 * r2 + 2 * g01 * g02 * g12 - r0 * g12 ^ 2 - r1 * g02 ^ 2
          - r2 * g01 ^ 2 =
        (r0 - g02) * (r1 - g12) * (r2 - (g02 + g12 - g01))
        + (r0 - g02) * (r1 - g12) * (g02 - g01)
        + (r0 - g02) * (r1 - g12) * (g12 - g01)
        + (r0 - g02) * (r1 - g12) * g01
        + (r0 - g02) * (r2 - (g02 + g12 - g01)) * (g12 - g01)
        + (r0 - g02) * (r2 - (g02 + g12 - g01)) * g01
        + (r0 - g02) * (g02 - g01) * (g12 - g01)
        + (r0 - g02) * (g02 - g01) * g01
        + (r1 - g12) * (r2 - (g02 + g12 - g01)) * (g02 - g01)
        + (r1 - g12) * (r2 - (g02 + g12 - g01)) * g01
        + (r1 - g12) * (g02 - g01) * (g12 - g01)
        + (r1 - g12) * (g12 - g01) * g01
        + (r2 - (g02 + g12 - g01)) * (g02 - g01) * (g12 - g01)
        + (r2 - (g02 + g12 - g01)) * (g02 - g01) * g01
        + (r2 - (g02 + g12 - g01)) * (g12 - g01) * g01
        + (g02 - g01) * (g12 - g01) * g01 := by
    ring
  rw [hdecomp]
  positivity

/-- **`q = 1` Schoenberg determinant** for an arbitrary four-point metric: the
Gromov-product (Schoenberg) matrix based at point `3` has nonnegative determinant.
This is the polyhedral fact that for `n ≤ 4` the metric cone equals the cut cone,
so every four-point metric is of (`1`-)negative type. -/
private lemma det_gromov_nonneg (r0 r1 r2 g01 g02 g12 : ℝ)
    (hg01 : 0 ≤ g01) (hg02 : 0 ≤ g02) (hg12 : 0 ≤ g12)
    (a01 : g01 ≤ r0) (b01 : g01 ≤ r1) (a02 : g02 ≤ r0) (b02 : g02 ≤ r2)
    (a12 : g12 ≤ r1) (b12 : g12 ≤ r2)
    (t0 : g01 + g02 - g12 ≤ r0) (t1 : g01 + g12 - g02 ≤ r1) (t2 : g02 + g12 - g01 ≤ r2) :
    0 ≤ r0 * r1 * r2 + 2 * g01 * g02 * g12 - r0 * g12 ^ 2 - r1 * g02 ^ 2 - r2 * g01 ^ 2 := by
  rcases le_total g01 g02 with h0102 | h0201
  · rcases le_total g01 g12 with h0112 | h1201
    · exact det_gromov_nonneg_of_g01_min r0 r1 r2 g01 g02 g12 hg01 h0102 h0112 a02 a12 t2
    · have h := det_gromov_nonneg_of_g01_min r1 r2 r0 g12 g01 g02 hg12 h1201
        (le_trans h1201 h0102) b01 b02 t0
      convert h using 1
      ring
  · rcases le_total g02 g12 with h0212 | h1202
    · have h := det_gromov_nonneg_of_g01_min r0 r2 r1 g02 g01 g12 hg02 h0201 h0212 a01 b12 t1
      convert h using 1
      ring
    · have h := det_gromov_nonneg_of_g01_min r1 r2 r0 g12 g01 g02 hg12
        (le_trans h1202 h0201) h1202 b01 b02 t0
      convert h using 1
      ring

lemma metric4_det_q1_nonneg (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) :
    0 ≤ schoenDet (d 0 3) (d 1 3) (d 2 3)
        ((d 0 3 + d 1 3 - d 0 1) / 2)
        ((d 0 3 + d 2 3 - d 0 2) / 2)
        ((d 1 3 + d 2 3 - d 1 2) / 2) := by
  unfold schoenDet
  have hs := hm.2.1
  have ht := hm.2.2.2
  exact det_gromov_nonneg (d 0 3) (d 1 3) (d 2 3)
    ((d 0 3 + d 1 3 - d 0 1) / 2) ((d 0 3 + d 2 3 - d 0 2) / 2) ((d 1 3 + d 2 3 - d 1 2) / 2)
    (by linarith [ht 0 3 1, hs 3 1]) (by linarith [ht 0 3 2, hs 3 2])
    (by linarith [ht 1 3 2, hs 3 2])
    (by linarith [ht 1 0 3, hs 1 0]) (by linarith [ht 0 1 3])
    (by linarith [ht 2 0 3, hs 2 0]) (by linarith [ht 0 2 3])
    (by linarith [ht 2 1 3, hs 2 1]) (by linarith [ht 1 2 3])
    (by linarith [ht 1 0 2, hs 1 0]) (by linarith [ht 0 1 2])
    (by linarith [ht 0 2 1, hs 2 1])

/-- **Every four-point metric has `1`-negative type.** -/
lemma metric4_one_negType (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) :
    HasNegType 1 d := by
  exact negType_of_schoenDet_nonneg one_pos (by norm_num) d hm
    (by simpa only [Real.rpow_one] using metric4_det_q1_nonneg d hm)

/-
The Gromov-product (Schoenberg) kernel of a four-point metric of `1`-negative
type has nonnegative quadratic form.
-/
lemma metric4_qpos_gram (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d)
    (h1 : HasNegType 1 d) :
    ExpKernel.QPos (fun i j : Fin 4 => (d i 3 + d j 3 - d i j) / 2) := by
  intro a
  set S := ∑ i, a i
  set c : Fin 4 → ℝ := fun k => a k - S * (if k = 3 then (1:ℝ) else 0)
  have hS : ∑ i, c i = 0 := by
    simp [c, S]
  have hle := h1 c hS
  simp only [Real.rpow_one] at hle ⊢
  simp [Fin.sum_univ_four] at hle ⊢
  simp +zetaDelta at *
  simp_all +decide [Fin.sum_univ_four, IsMetric4]
  nlinarith! [sq_nonneg (a 0 + a 1 + a 2 + a 3)]

/-- **The case `0 < q ≤ 1` (Blumenthal): every four-point metric has `q`-negative
type.**

For `q = 1` this is `metric4_one_negType`.  For `0 < q < 1` it follows from the
`1`-negative type by downward closure (`ExpKernel.qpos_downward`): writing the
metric as `d i j = B i i + B j j - 2 B i j` with `B` the Gromov-product kernel
(positive semidefinite by `metric4_qpos_gram`), the snowflake `d ^ q` is again of
negative type. -/
lemma blumenthal_negType {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) :
    HasNegType q d := by
  have h1 : HasNegType 1 d := metric4_one_negType d hm
  rcases eq_or_lt_of_le hq1 with rfl | hlt
  · exact h1
  · intro a ha
    have hsymmB : ∀ i j : Fin 4, (fun i j => (d i 3 + d j 3 - d i j) / 2) i j
        = (fun i j => (d i 3 + d j 3 - d i j) / 2) j i := by
      intro i j
      simp only []
      rw [hm.2.1 j i]
      ring
    have hrelB : ∀ i j : Fin 4, d i j
        = (fun i j => (d i 3 + d j 3 - d i j) / 2) i i
        + (fun i j => (d i 3 + d j 3 - d i j) / 2) j j
        - 2 * (fun i j => (d i 3 + d j 3 - d i j) / 2) i j := by
      intro i j
      simp only []
      rw [hm.1 i, hm.1 j]
      ring
    exact ExpKernel.qpos_downward hsymmB (metric4_qpos_gram d hm h1) hrelB
      (fun i j => hm.2.2.1 i j) ⟨hq0, hlt⟩ a ha

/-- **Four-point Ptolemaic snowflake theorem** (`thm:q5-four-point-ptolemaic`).
Every four-point Ptolemaic metric has `q`-negative type for `0 < q ≤ log₂ 3`. -/
theorem four_point_ptolemaic_negType {q : ℝ} (hq0 : 0 < q) (hq : q ≤ Real.logb 2 3)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) (hp : IsPtolemaic4 d) :
    HasNegType q d := by
  by_cases h1 : q ≤ 1
  · exact blumenthal_negType hq0 h1 d hm
  · exact negType_ge_one (le_of_lt (lt_of_not_ge h1)) hq d hm hp

end Ptolemaic

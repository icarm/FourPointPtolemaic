import Mathlib
import RequestProject.Main
import RequestProject.ExpKernel

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

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
  intro x y z;
  by_cases hA' : A = 0;
  · simp_all +decide;
    by_cases hB' : B = 0;
    · simp_all +decide [ show w = 0 by nlinarith ];
      positivity;
    · cases lt_or_gt_of_ne hB' <;> nlinarith [ sq_nonneg ( B * y + w * z ), sq_nonneg ( C * z + w * y ) ];
  · -- Since $A > 0$, we can complete the square for the quadratic form.
    have h_complete_square : A * (A * x ^ 2 + B * y ^ 2 + C * z ^ 2 + 2 * u * x * y + 2 * v * x * z + 2 * w * y * z) = (A * x + u * y + v * z) ^ 2 + (B * A - u ^ 2) * y ^ 2 + (C * A - v ^ 2) * z ^ 2 + 2 * (w * A - u * v) * y * z := by
      ring;
    have h_complete_square : (B * A - u ^ 2) * y ^ 2 + (C * A - v ^ 2) * z ^ 2 + 2 * (w * A - u * v) * y * z ≥ 0 := by
      have h_complete_square : (B * A - u ^ 2) * (C * A - v ^ 2) ≥ (w * A - u * v) ^ 2 := by
        nlinarith [ mul_self_pos.mpr hA' ];
      by_cases h_case : B * A - u ^ 2 = 0;
      · norm_num [ show w * A - u * v = 0 by nlinarith ] at * ; nlinarith [ mul_self_nonneg z ] ;
      · by_cases h_case : B * A - u ^ 2 > 0;
        · nlinarith [ sq_nonneg ( ( B * A - u ^ 2 ) * y + ( w * A - u * v ) * z ), mul_self_pos.2 ‹_› ];
        · exact False.elim <| h_case <| lt_of_le_of_ne ( by linarith ) <| Ne.symm ‹_›;
    nlinarith [ mul_self_pos.mpr hA' ]

/-
Elementary determinant form for star metrics: for `η₁₂, η₁₃, η₂₃ ∈ [0,1]`,
`1 - (η₁₂² + η₁₃² + η₂₃² + η₁₂ η₁₃ η₂₃)/4 ≥ 0`.
-/
lemma star_det_nonneg (a b c : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ 1 - (a ^ 2 + b ^ 2 + c ^ 2 + a * b * c) / 4 := by
  nlinarith [ mul_nonneg ha0 hb0 ]

/-
`3 ^ (log₃ 2) = 2`.
-/
lemma three_rpow_logb : (3 : ℝ) ^ (Real.logb 3 2) = 2 := by
  rw [ Real.rpow_logb ] <;> norm_num

/-
Numeric bounds: `1/2 < log₃ 2 < 2/3`.
-/
lemma logb32_bounds : 1 / 2 < Real.logb 3 2 ∧ Real.logb 3 2 < 2 / 3 := by
  rw [ Real.logb ];
  constructor <;> rw [ div_lt_div_iff₀ ( by positivity ) ( by positivity ) ]; all_goals norm_num [ mul_comm, ← Real.log_rpow, Real.log_lt_log ]

/-
The crossing function `Ξ(v) = (1+v+v²)/((1+2v)(2+v))` is antitone on `[0,1]`.
-/
lemma xi_antitoneOn :
    AntitoneOn (fun v : ℝ => (1 + v + v ^ 2) / ((1 + 2 * v) * (2 + v))) (Set.Icc (0 : ℝ) 1) := by
  intros v hv w hw hvw;
  rw [ div_le_div_iff₀ ] <;> nlinarith [ hv.1, hv.2, hw.1, hw.2, mul_le_mul_of_nonneg_left hvw hv.1 ]

/-
Core unimodality inequality: with `k₀ = 1 - log₃ 2 ∈ (1/3, 1/2)`,
the function `Θ(v) = log(1 + v/2) - k₀ · log(1 + v + v²)` is nonnegative on `[0,1]`.
It vanishes at the endpoints `v=0` and `v=1`, is increasing then decreasing.
-/
lemma theta_nonneg (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ Real.log (1 + v / 2) - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2) := by
  -- By the intermediate value theorem, there exists $v^* \in [0, 1]$ such that $\Xi(v^*) = k₀$.
  obtain ⟨v_star, hv_star⟩ : ∃ v_star ∈ Set.Icc (0 : ℝ) 1, (1 + v_star + v_star ^ 2) / ((1 + 2 * v_star) * (2 + v_star)) = 1 - Real.logb 3 2 := by
    apply_rules [ intermediate_value_Icc' ] <;> norm_num;
    · exact ContinuousOn.div ( Continuous.continuousOn ( by continuity ) ) ( Continuous.continuousOn ( by continuity ) ) fun x hx => by nlinarith [ hx.1, hx.2 ] ;
    · constructor <;> linarith [ logb32_bounds ];
  -- For $v \in [0, v^*]$, $\Xi(v) \geq \Xi(v^*) = k₀$ so $\Theta'(v) \geq 0$.
  have h_deriv_nonneg : ∀ v ∈ Set.Icc (0 : ℝ) v_star, 0 ≤ deriv (fun v => Real.log (1 + v / 2) - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2)) v := by
    intro v hv ;
    have h_deriv_nonneg : (1 + v + v ^ 2) / ((1 + 2 * v) * (2 + v)) ≥ 1 - Real.logb 3 2 := by
      rw [ ← hv_star.2 ] ; exact xi_antitoneOn ( by constructor <;> linarith [ hv.1, hv.2, hv_star.1.1, hv_star.1.2 ] ) ( by constructor <;> linarith [ hv.1, hv.2, hv_star.1.1, hv_star.1.2 ] ) hv.2;
    norm_num [ add_assoc, show ( 1 + v / 2 ) ≠ 0 from by linarith [ hv.1 ], show ( 1 + v + v ^ 2 ) ≠ 0 from by nlinarith [ hv.1 ] ];
    norm_num [ show 1 + v / 2 ≠ 0 from by linarith [ hv.1 ], show 1 + ( v + v ^ 2 ) ≠ 0 from by nlinarith [ hv.1 ] ];
    rw [ mul_div, div_le_div_iff₀ ] <;> try nlinarith [ hv.1, hv.2 ];
    rw [ ge_iff_le, le_div_iff₀ ] at h_deriv_nonneg <;> nlinarith [ hv.1, hv.2, hv_star.1.1, hv_star.1.2 ];
  -- For $v \in [v^*, 1]$, $\Xi(v) \leq k₀$ so $\Theta'(v) \leq 0$.
  have h_deriv_nonpos : ∀ v ∈ Set.Icc v_star 1, deriv (fun v => Real.log (1 + v / 2) - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2)) v ≤ 0 := by
    intro v hv
    have h_deriv : deriv (fun v => Real.log (1 + v / 2) - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2)) v = (1 / (2 + v)) - (1 - Real.logb 3 2) * ((1 + 2 * v) / (1 + v + v ^ 2)) := by
      norm_num [ add_assoc, show v + 1 + v ^ 2 ≠ 0 from by nlinarith [ hv.1, hv.2, hv_star.1.1, hv_star.1.2 ], show 2 + v ≠ 0 from by nlinarith [ hv.1, hv.2, hv_star.1.1, hv_star.1.2 ] ];
      norm_num [ show 1 + v / 2 ≠ 0 from by nlinarith [ hv.1, hv.2, hv_star.1.1, hv_star.1.2 ], show 1 + ( v + v ^ 2 ) ≠ 0 from by nlinarith [ hv.1, hv.2, hv_star.1.1, hv_star.1.2 ] ] ; ring_nf;
      rw [ show 2 + v = 2 * ( 1 + v * ( 1 / 2 ) ) by ring, mul_inv ] ; ring;
    have h_antitone : (1 + v + v ^ 2) / ((1 + 2 * v) * (2 + v)) ≤ (1 + v_star + v_star ^ 2) / ((1 + 2 * v_star) * (2 + v_star)) := by
      exact xi_antitoneOn ( show v_star ∈ Set.Icc 0 1 from hv_star.1 ) ( show v ∈ Set.Icc 0 1 from ⟨ by linarith [ hv.1, hv_star.1.1 ], by linarith [ hv.2, hv_star.1.2 ] ⟩ ) hv.1;
    simp_all +decide [ div_eq_mul_inv ];
    convert mul_le_mul_of_nonneg_right h_antitone ( show 0 ≤ ( 1 + 2 * v ) * ( 1 + v + v ^ 2 ) ⁻¹ by exact mul_nonneg ( by linarith ) ( inv_nonneg.mpr ( by nlinarith ) ) ) using 1 ; ring_nf;
    field_simp;
    rw [ div_eq_div_iff ] <;> nlinarith only [ hv, hv_star.1.1, hv_star.1.2, pow_two_nonneg ( v - v_star ), pow_two_nonneg ( v + v_star ) ];
  -- Therefore, $\Theta(v)$ is monotone nondecreasing on $[0, v^*]$ and nonincreasing on $[v^*, 1]$.
  have h_monotone : ∀ v ∈ Set.Icc (0 : ℝ) v_star, Real.log (1 + v / 2) - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2) ≥ Real.log (1 + 0 / 2) - (1 - Real.logb 3 2) * Real.log (1 + 0 + 0 ^ 2) := by
    intros v hv; by_contra h_contra; push_neg at h_contra; (
    have := exists_deriv_eq_slope ( f := fun v => Real.log ( 1 + v / 2 ) - ( 1 - Real.logb 3 2 ) * Real.log ( 1 + v + v ^ 2 ) ) ( show v > 0 from hv.1.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; norm_num at *;
    contrapose! this;
    exact ⟨ continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub ( ContinuousAt.log ( continuousAt_const.add ( continuousAt_id.div_const _ ) ) ( by linarith [ hx.1 ] ) ) ( ContinuousAt.mul continuousAt_const ( ContinuousAt.log ( continuousAt_const.add continuousAt_id |> ContinuousAt.add <| continuousAt_id.pow 2 ) ( by nlinarith [ hx.1 ] ) ) ), fun x hx => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.sub ( DifferentiableAt.log ( by norm_num ) <| by linarith [ hx.1 ] ) <| DifferentiableAt.mul ( differentiableAt_const _ ) <| DifferentiableAt.log ( by norm_num [ add_assoc ] ) <| by nlinarith [ hx.1 ], fun c hc => by rw [ ne_eq, eq_div_iff ] <;> nlinarith [ h_deriv_nonneg c ( by linarith ) ( by linarith ) ] ⟩);
  have h_antitone : ∀ v ∈ Set.Icc v_star 1, Real.log (1 + v / 2) - (1 - Real.logb 3 2) * Real.log (1 + v + v ^ 2) ≥ Real.log (1 + 1 / 2) - (1 - Real.logb 3 2) * Real.log (1 + 1 + 1 ^ 2) := by
    intros v hv
    by_contra h_contra;
    have := exists_deriv_eq_slope ( f := fun v => Real.log ( 1 + v / 2 ) - ( 1 - Real.logb 3 2 ) * Real.log ( 1 + v + v ^ 2 ) ) ( show v < 1 from hv.2.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; norm_num at *;
    contrapose! this;
    refine' ⟨ _, _, _ ⟩;
    · exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub ( ContinuousAt.log ( continuousAt_const.add ( continuousAt_id.div_const _ ) ) ( by nlinarith [ hx.1, hx.2 ] ) ) ( ContinuousAt.mul continuousAt_const ( ContinuousAt.log ( continuousAt_const.add continuousAt_id |> ContinuousAt.add <| continuousAt_id.pow 2 ) ( by nlinarith [ hx.1, hx.2 ] ) ) ) ;
    · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( DifferentiableAt.log ( by norm_num ) ( by linarith [ hx.1 ] ) ) ( DifferentiableAt.mul ( differentiableAt_const _ ) ( DifferentiableAt.log ( by norm_num [ add_assoc ] ) ( by nlinarith [ hx.1 ] ) ) ) );
    · exact fun c hc => by rw [ ne_eq, eq_div_iff ] <;> nlinarith [ h_deriv_nonpos c ( by linarith ) ( by linarith ) ] ;
  by_cases hv : v ≤ v_star;
  · exact le_trans ( by norm_num ) ( h_monotone v ⟨ hv0, hv ⟩ );
  · refine le_trans ?_ ( h_antitone v ⟨ by linarith, by linarith ⟩ ) ; norm_num [ Real.logb ];
    rw [ Real.log_div ] <;> ring_nf <;> norm_num

/-
Key inequality behind `φ' ≥ 0`: for `t ≥ 1`,
`2·(t²+t+1)^(1-p₀) ≤ (2t+1)·t^(1-2p₀)` where `p₀ = log₃ 2`.
-/
lemma psi_key (t : ℝ) (ht : 1 ≤ t) :
    2 * (t ^ 2 + t + 1) ^ (1 - Real.logb 3 2)
      ≤ (2 * t + 1) * t ^ (1 - 2 * Real.logb 3 2) := by
  -- Apply the lemma `theta_nonneg` with $v = 1/t$ and $t = t$.
  have h_lemma : 0 ≤ Real.log (1 + 1 / (2 * t)) - (1 - Real.logb 3 2) * Real.log (1 + 1 / t + 1 / t^2) := by
    convert theta_nonneg ( 1 / t ) ( by positivity ) ( by rw [ div_le_iff₀ ( by positivity ) ] ; linarith ) using 1 ; ring_nf;
  rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ), Real.log_rpow ( by positivity ) ];
  rw [ show ( t ^ 2 + t + 1 : ℝ ) = t ^ 2 * ( 1 + 1 / t + 1 / t ^ 2 ) by nlinarith [ one_div_mul_cancel ( show t ≠ 0 by linarith ), one_div_pow t 2 ], Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ] ; ring_nf at *;
  rw [ show ( 1 + t * 2 ) = 2 * ( 1 + t⁻¹ * ( 1 / 2 ) ) * t by nlinarith [ mul_inv_cancel₀ ( by linarith : t ≠ 0 ) ], Real.log_mul, Real.log_mul ] <;> first | positivity | ring_nf at * ; linarith [ Real.log_pos one_lt_two ] ;

/-
The base case of the star inequality (single variable, exponent `p₀ = log₃ 2`).
For `t ≥ 0`, `t ^ (2 * log₃ 2) + 1 ≤ (t^2 + t + 1) ^ (log₃ 2)`.
-/
lemma star_single_p0 (t : ℝ) (ht : 0 ≤ t) :
    t ^ (2 * Real.logb 3 2) + 1 ≤ (t ^ 2 + t + 1) ^ (Real.logb 3 2) := by
  by_cases ht1 : t ≥ 1;
  · -- For $t \geq 1$, we use the fact that $\phi'(t) \geq 0$ to show that $\phi(t)$ is non-decreasing.
    have h_deriv_nonneg : ∀ t : ℝ, 1 ≤ t → deriv (fun t : ℝ => (t^2 + t + 1) ^ (Real.logb 3 2) - t ^ (2 * Real.logb 3 2) - 1) t ≥ 0 := by
      intro t ht1; norm_num [ show t ^ 2 + t + 1 ≠ 0 by positivity, show t ≠ 0 by positivity ];
      have := psi_key t ht1;
      rw [ show ( 1 - Real.logb 3 2 ) = - ( Real.logb 3 2 - 1 ) by ring, Real.rpow_neg ( by positivity ), show ( 1 - 2 * Real.logb 3 2 ) = - ( 2 * Real.logb 3 2 - 1 ) by ring, Real.rpow_neg ( by positivity ) ] at this;
      field_simp at this;
      convert mul_le_mul_of_nonneg_left this ( show 0 ≤ Real.logb 3 2 by exact Real.logb_nonneg ( by norm_num ) ( by norm_num ) ) using 1 <;> ring_nf;
    -- Since $\phi(t)$ is non-decreasing for $t \geq 1$, we have $\phi(t) \geq \phi(1)$.
    have h_phi_ge_phi1 : ∀ t : ℝ, 1 ≤ t → (t^2 + t + 1) ^ (Real.logb 3 2) - t ^ (2 * Real.logb 3 2) - 1 ≥ (1^2 + 1 + 1) ^ (Real.logb 3 2) - 1 ^ (2 * Real.logb 3 2) - 1 := by
      intro t ht; by_contra h_contra; push_neg at h_contra; (
      have := exists_deriv_eq_slope ( f := fun t : ℝ => ( t^2 + t + 1 ) ^ Real.logb 3 2 - t ^ ( 2 * Real.logb 3 2 ) - 1 ) ( show t > 1 from lt_of_le_of_ne ht <| Ne.symm <| by rintro rfl; norm_num at h_contra ) ; norm_num at *;
      contrapose! this;
      exact ⟨ ContinuousOn.sub ( ContinuousOn.sub ( ContinuousOn.rpow ( ContinuousOn.add ( ContinuousOn.add ( continuousOn_id.pow 2 ) continuousOn_id ) continuousOn_const ) continuousOn_const <| by intro x hx; exact Or.inr <| by linarith [ Real.logb_pos ( show 3 > 1 by norm_num ) ( show 2 > 1 by norm_num ) ] ) <| ContinuousOn.rpow continuousOn_id continuousOn_const <| by intro x hx; exact Or.inr <| by linarith [ Real.logb_pos ( show 3 > 1 by norm_num ) ( show 2 > 1 by norm_num ) ] ) continuousOn_const, fun x hx => DifferentiableAt.differentiableWithinAt <| by norm_num [ show x ^ 2 + x + 1 ≠ 0 from by nlinarith, show x ≠ 0 from by linarith [ hx.1 ] ], fun c hc => by rw [ ne_eq, eq_div_iff ] <;> nlinarith [ h_deriv_nonneg c <| by linarith ] ⟩);
    have := h_phi_ge_phi1 t ht1; norm_num [ Real.rpow_logb ] at *; linarith;
  · by_cases ht0 : t = 0;
    · norm_num [ ht0, show Real.logb 3 2 ≠ 0 by exact ne_of_gt ( Real.logb_pos ( by norm_num ) ( by norm_num ) ) ];
    · -- For $0 < t < 1$, we use the symmetry argument.
      have h_symm : (t ^ 2 + t + 1) ^ (Real.logb 3 2) = t ^ (2 * Real.logb 3 2) * ((1 / t ^ 2 + 1 / t + 1) ^ (Real.logb 3 2)) := by
        rw [ Real.rpow_mul ] <;> norm_num [ ht, ht0 ];
        rw [ ← Real.mul_rpow ( by positivity ) ( by positivity ) ] ; congr ; nlinarith [ mul_inv_cancel₀ ht0, mul_inv_cancel₀ ( pow_ne_zero 2 ht0 ) ];
      -- By the properties of the function $\phi$, we know that $\phi(1/t) \geq 0$ for $t \geq 1$.
      have h_phi_inv : ∀ t : ℝ, 1 ≤ t → (t ^ 2 + t + 1) ^ (Real.logb 3 2) ≥ t ^ (2 * Real.logb 3 2) + 1 := by
        intro t ht1
        have h_phi_inv : ∀ t : ℝ, 1 ≤ t → deriv (fun t => (t ^ 2 + t + 1) ^ (Real.logb 3 2) - t ^ (2 * Real.logb 3 2) - 1) t ≥ 0 := by
          intro t ht1; norm_num [ show t ^ 2 + t + 1 ≠ 0 by positivity, show t ≠ 0 by positivity ];
          have := psi_key t ht1;
          rw [ show ( 1 - Real.logb 3 2 ) = - ( Real.logb 3 2 - 1 ) by ring, Real.rpow_neg ( by positivity ), show ( 1 - 2 * Real.logb 3 2 ) = - ( 2 * Real.logb 3 2 - 1 ) by ring, Real.rpow_neg ( by positivity ) ] at this;
          field_simp at this;
          ring_nf at this ⊢;
          nlinarith [ show 0 < Real.logb 3 2 by exact Real.logb_pos ( by norm_num ) ( by norm_num ) ];
        by_contra h_contra;
        have := exists_deriv_eq_slope ( f := fun t => ( t ^ 2 + t + 1 ) ^ Real.logb 3 2 - t ^ ( 2 * Real.logb 3 2 ) - 1 ) ( show t > 1 from ht1.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; norm_num at *;
        contrapose! this;
        exact ⟨ ContinuousOn.sub ( ContinuousOn.sub ( ContinuousOn.rpow ( ContinuousOn.add ( ContinuousOn.add ( continuousOn_id.pow 2 ) continuousOn_id ) continuousOn_const ) continuousOn_const <| by intro x hx; exact Or.inr <| by linarith [ Real.logb_pos ( show 3 > 1 by norm_num ) ( show 2 > 1 by norm_num ) ] ) <| ContinuousOn.rpow continuousOn_id continuousOn_const <| by intro x hx; exact Or.inr <| by linarith [ Real.logb_pos ( show 3 > 1 by norm_num ) ( show 2 > 1 by norm_num ) ] ) continuousOn_const, fun x hx => DifferentiableAt.differentiableWithinAt <| by norm_num [ show x ^ 2 + x + 1 ≠ 0 from by nlinarith, show x ≠ 0 from by linarith [ hx.1 ] ], fun c hc => by rw [ ne_eq, eq_div_iff ] <;> nlinarith [ h_phi_inv c <| by linarith ] ⟩;
      have := h_phi_inv ( 1 / t ) ( by rw [ le_div_iff₀ ( by positivity ) ] ; linarith ) ; simp_all +decide [ division_def ] ;
      rw [ Real.inv_rpow ( by positivity ) ] at this;
      nlinarith [ Real.rpow_pos_of_pos ( show 0 < t by positivity ) ( 2 * Real.logb 3 2 ), mul_inv_cancel₀ ( ne_of_gt ( Real.rpow_pos_of_pos ( show 0 < t by positivity ) ( 2 * Real.logb 3 2 ) ) ) ]

/-
Monotonicity in the exponent: the single-variable star inequality for `p₀ = log₃ 2`
upgrades to all `p ∈ [log₃ 2, 1]`.
For `t ≥ 0` and `log₃ 2 ≤ p ≤ 1`, `t ^ (2*p) + 1 ≤ (t^2 + t + 1) ^ p`.
-/
lemma star_single {p t : ℝ} (hp0 : Real.logb 3 2 ≤ p) (_hp1 : p ≤ 1) (ht : 0 ≤ t) :
    t ^ (2 * p) + 1 ≤ (t ^ 2 + t + 1) ^ p := by
  by_cases ht1 : t ≤ 1;
  · have h_monotone : t ^ (2 * p) + 1 ≤ (t ^ 2 + t + 1) ^ (Real.logb 3 2) := by
      have h_monotone : t ^ (2 * p) ≤ t ^ (2 * Real.logb 3 2) := by
        by_cases ht0 : t = 0;
        · norm_num [ ht0, show p ≠ 0 by linarith [ Real.logb_pos ( show ( 3 : ℝ ) > 1 by norm_num ) ( show ( 2 : ℝ ) > 1 by norm_num ) ], show Real.logb 3 2 ≠ 0 by exact ne_of_gt ( Real.logb_pos ( show ( 3 : ℝ ) > 1 by norm_num ) ( show ( 2 : ℝ ) > 1 by norm_num ) ) ];
        · exact Real.rpow_le_rpow_of_exponent_ge ( by positivity ) ht1 ( by linarith );
      have h_monotone : t ^ (2 * Real.logb 3 2) + 1 ≤ (t ^ 2 + t + 1) ^ (Real.logb 3 2) := by
        convert star_single_p0 t ht using 1;
      linarith;
    exact h_monotone.trans ( Real.rpow_le_rpow_of_exponent_le ( by nlinarith ) hp0 );
  · -- For $t > 1$ and $p \ge \log_3 2$, we use the fact that $t^{2p} + 1 \le (t^2 + t + 1)^p$ follows from the monotonicity of the function $f(x) = x^p - x^{p₀}$ on $[1, \infty)$.
    have h_mono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → x^p - x^(Real.logb 3 2) ≤ y^p - y^(Real.logb 3 2) := by
      -- The derivative of $f(x) = x^p - x^{p₀}$ is $f'(x) = p x^{p-1} - p₀ x^{p₀-1}$.
      have h_deriv : ∀ x : ℝ, 1 ≤ x → deriv (fun x => x^p - x^(Real.logb 3 2)) x ≥ 0 := by
        intro x hx; norm_num [ show x ≠ 0 by linarith ] ; ring_nf;
        exact mul_le_mul hp0 ( Real.rpow_le_rpow_of_exponent_le hx ( by linarith ) ) ( by positivity ) ( by linarith [ Real.logb_nonneg ( show 3 > 1 by norm_num ) ( show 2 ≥ 1 by norm_num ) ] );
      intros x y hx hy; by_contra h_contra; push_neg at h_contra; (
      have := exists_deriv_eq_slope ( f := fun x => x ^ p - x ^ Real.logb 3 2 ) ( show x < y from hy.lt_of_ne ( by rintro rfl; linarith ) ) ; norm_num at *;
      exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun z hz => by exact ContinuousAt.sub ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [ hz.1 ] ) ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [ hz.1 ] ) ) ( by exact fun z hz => by exact DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.sub ( DifferentiableAt.rpow ( differentiableAt_id ) ( by norm_num ) <| by linarith [ hz.1 ] ) ( DifferentiableAt.rpow ( differentiableAt_id ) ( by norm_num ) <| by linarith [ hz.1 ] ) ) ) ( by rintro ⟨ c, ⟨ hxc, hcy ⟩, hcd ⟩ ; rw [ eq_div_iff ] at hcd <;> nlinarith [ h_deriv c <| by linarith ] ));
    have := h_mono ( t ^ 2 ) ( t ^ 2 + t + 1 ) ( by nlinarith ) ( by nlinarith ) ; simp_all +decide [ Real.rpow_mul ];
    have := star_single_p0 t ht; norm_num [ Real.rpow_mul ht ] at *; linarith;

/-
Two-variable homogeneous form of the star inequality.
For `log₃ 2 ≤ p ≤ 1` and `u, v ≥ 0`,
`u^p + v^p ≤ (u + v + Real.sqrt (u*v))^p`.
-/
lemma star_uv {p : ℝ} (hp0 : Real.logb 3 2 ≤ p) (hp1 : p ≤ 1)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u ^ p + v ^ p ≤ (u + v + Real.sqrt (u * v)) ^ p := by
  by_cases hu' : u = 0 <;> by_cases hv' : v = 0 <;> simp_all +decide [ Real.sqrt_mul hu ];
  · rw [ Real.zero_rpow ( by linarith [ Real.logb_pos ( show 3 > 1 by norm_num ) ( show 2 > 1 by norm_num ) ] ) ];
  · rw [ Real.zero_rpow ( by linarith [ Real.logb_pos ( show 3 > 1 by norm_num ) ( show 2 > 1 by norm_num ) ] ) ];
  · rw [ Real.zero_rpow ( by linarith [ Real.logb_pos ( show 3 > 1 by norm_num ) ( show 2 > 1 by norm_num ) ] ) ];
  · -- Set $t := \sqrt{\frac{u}{v}} \geq 0$, so $t^2 = \frac{u}{v}$ and $\sqrt{uv} = v t$.
    obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ u = v * t^2 := by
      exact ⟨ Real.sqrt ( u / v ), Real.sqrt_nonneg _, by rw [ Real.sq_sqrt ( div_nonneg hu hv ), mul_div_cancel₀ _ hv' ] ⟩;
    -- Then $u^p + v^p = v^p (t^{2p} + 1)$ and $(u + v + \sqrt{uv})^p = v^p (t^2 + t + 1)^p$.
    have h_exp : u ^ p + v ^ p = v ^ p * (t ^ (2 * p) + 1) ∧ (u + v + Real.sqrt (u * v)) ^ p = v ^ p * (t ^ 2 + t + 1) ^ p := by
      constructor <;> ring_nf;
      · rw [ ht.2, Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith ) ] ; ring_nf;
      · rw [ ← Real.mul_rpow ( by positivity ) ( by nlinarith ) ] ; rw [ ht.2 ] ; ring_nf;
        rw [ Real.sqrt_mul ( by positivity ), Real.sqrt_sq ( by positivity ), Real.sqrt_sq ( by linarith ) ] ; ring_nf;
    rw [ ← Real.sqrt_mul hu ] ; exact h_exp.1.symm ▸ h_exp.2.symm ▸ mul_le_mul_of_nonneg_left ( star_single hp0 hp1 ht.1 ) ( by positivity ) ;

/-
**Star inequality** (Lemma `lem:q5-star`).
For `1 ≤ q ≤ log₂ 3` and `a, b ≥ 0`,
`(a + b)^q ≤ a^q + b^q + (a*b)^(q/2)`.
-/
lemma star_inequality {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ q ≤ a ^ q + b ^ q + (a * b) ^ (q / 2) := by
  -- Set $p := 1 / q$.
  set p := 1 / q with hp;
  -- Apply star_uv with this p, u := a^q, v := b^q (both ≥ 0).
  have h_star_uv : (a^q)^p + (b^q)^p ≤ (a^q + b^q + Real.sqrt ((a^q) * (b^q)))^p := by
    convert star_uv _ _ _ _ ( Real.rpow_nonneg ha q ) ( Real.rpow_nonneg hb q ) using 1 <;> ring_nf;
    · rw [ Real.logb, div_le_div_iff₀ ] <;> norm_num;
      · rw [ Real.logb ] at hq ; rw [ le_div_iff₀ ( Real.log_pos ( by norm_num ) ) ] at hq ; linarith;
      · positivity;
      · linarith;
    · exact div_le_self zero_le_one hq1;
  convert Real.rpow_le_rpow _ h_star_uv ( show 0 ≤ q by positivity ) using 1;
  · rw [ ← Real.rpow_mul ( by positivity ), ← Real.rpow_mul ( by positivity ), mul_one_div_cancel ( by positivity ), Real.rpow_one, Real.rpow_one ];
  · rw [ ← Real.rpow_mul ( by positivity ), one_div_mul_cancel ( by positivity ), Real.rpow_one ];
    rw [ ← Real.mul_rpow ( by positivity ) ( by positivity ), Real.sqrt_eq_rpow, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
  · positivity

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
  intro c hc; simp_all +decide [ Fin.sum_univ_four ] ;
  rw [ show c 3 = -c 0 - c 1 - c 2 by linarith ] ; ring_nf at *;
  norm_num [ hq0.ne' ] ; linarith [ hPSD ( c 0 ) ( c 1 ) ( c 2 ) ] ;

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
  set Z := s ^ (q / 2);
  -- Then $p^q = X^2$, $r^q = Y^2$, $s^q = Z^2$ (since $(p^{q/2})^2 = p^{(q/2)*2} = p^q$, using Real.rpow_natCast / Real.rpow_mul with $p \geq 0$).
  have hX : X^2 = p^q := by
    rw [ ← Real.rpow_natCast, ← Real.rpow_mul hp ] ; ring_nf
  have hY : Y^2 = r^q := by
    rw [ ← Real.rpow_natCast, ← Real.rpow_mul hr ] ; ring_nf
  have hZ : Z^2 = s^q := by
    rw [ ← Real.rpow_natCast, ← Real.rpow_mul hs ] ; ring_nf;
  -- We show the snowflaked triangle inequalities, i.e. each factor ≥ 0:
  have hX_Y_Z : X + Y - Z ≥ 0 ∧ Z + X - Y ≥ 0 ∧ Z + Y - X ≥ 0 := by
    refine' ⟨ _, _, _ ⟩ <;> norm_num;
    · exact le_trans ( Real.rpow_le_rpow ( by positivity ) h1 ( by positivity ) ) ( by simpa using Real.rpow_add_le_add_rpow ( by positivity ) ( by positivity ) ( by positivity ) ( by linarith ) );
    · exact le_trans ( Real.rpow_le_rpow ( by positivity ) ( by linarith : r ≤ s + p ) ( by positivity ) ) ( by simpa using Real.rpow_add_le_add_rpow hs hp ( by positivity ) ( by linarith ) );
    · exact le_trans ( Real.rpow_le_rpow ( by positivity ) ( show p ≤ s + r by linarith ) ( by positivity ) ) ( by simpa using Real.rpow_add_le_add_rpow ( by positivity ) ( by positivity ) ( by positivity ) ( by linarith ) );
  nlinarith [ mul_nonneg hX_Y_Z.1 ( mul_nonneg hX_Y_Z.2.1 hX_Y_Z.2.2 ) ]

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
  set w : ℝ → ℝ := fun v => ∑ i ∈ Finset.univ.filter (fun i => x i = v), c i;
  -- Claim 2: $\sum_{i,j} c_i c_j |x_i - x_j|^q = \sum_{v,u} w(v) w(u) |v - u|^q$.
  have h_sum : ∑ i, ∑ j, c i * c j * |x i - x j| ^ q = ∑ v ∈ Finset.image x Finset.univ, ∑ u ∈ Finset.image x Finset.univ, w v * w u * |v - u| ^ q := by
    simp +zetaDelta at *;
    simp +decide only [Finset.sum_sigma', Finset.univ_sigma_univ, Finset.sum_mul _ _ _, Finset.mul_sum];
    refine' Finset.sum_bij ( fun i hi => ⟨ x i.fst, x i.snd, i.fst, i.snd ⟩ ) _ _ _ _ <;> aesop;
  -- By NegType.real_finite_negative_type hq0 hq2 S w (Claim 1), the RHS ≤ 0, hence the LHS ≤ 0 by Claim 2.
  apply h_sum.symm ▸ NegType.real_finite_negative_type hq0 hq2 (Finset.image x Finset.univ) w (by
  rw [ ← hc, Finset.sum_image' ] ; aesop)

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
  refine negType_of_schoenberg ?_ ?_ ?_ ?_ ?_;
  · linarith;
  · exact hm.2.1;
  · exact hm.1;
  · intro a0 a1 a2
    set ρ0 := d 0 3
    set ρ1 := d 1 3
    set ρ2 := d 2 3
    have hρ0 : 0 ≤ ρ0 := by
      exact hm.2.2.1 _ _
    have hρ1 : 0 ≤ ρ1 := by
      exact hm.2.2.1 _ _
    have hρ2 : 0 ≤ ρ2 := by
      exact hm.2.2.1 _ _;
    -- Introduce η01, η02, η12 ∈ [0,1] and S01, S02, S12 ≥ 0 as in the provided solution.
    obtain ⟨η01, η02, η12, hη01, hη02, hη12, hS01, hS02, hS12⟩ : ∃ η01 η02 η12 S01 S02 S12 : ℝ,
      0 ≤ η01 ∧ η01 ≤ 1 ∧ 0 ≤ η02 ∧ η02 ≤ 1 ∧ 0 ≤ η12 ∧ η12 ≤ 1 ∧
      0 ≤ S01 ∧ 0 ≤ S02 ∧ 0 ≤ S12 ∧
      (ρ0 + ρ1) ^ q = ρ0 ^ q + ρ1 ^ q + η01 * S01 ∧
      (ρ0 + ρ2) ^ q = ρ0 ^ q + ρ2 ^ q + η02 * S02 ∧
      (ρ1 + ρ2) ^ q = ρ1 ^ q + ρ2 ^ q + η12 * S12 ∧
      S01 ^ 2 = ρ0 ^ q * ρ1 ^ q ∧
      S02 ^ 2 = ρ0 ^ q * ρ2 ^ q ∧
      S12 ^ 2 = ρ1 ^ q * ρ2 ^ q ∧
      S01 * S02 * S12 = ρ0 ^ q * ρ1 ^ q * ρ2 ^ q := by
        refine' ⟨ ( ( ρ0 + ρ1 ) ^ q - ρ0 ^ q - ρ1 ^ q ) / Real.sqrt ( ρ0 ^ q * ρ1 ^ q ), ( ( ρ0 + ρ2 ) ^ q - ρ0 ^ q - ρ2 ^ q ) / Real.sqrt ( ρ0 ^ q * ρ2 ^ q ), ( ( ρ1 + ρ2 ) ^ q - ρ1 ^ q - ρ2 ^ q ) / Real.sqrt ( ρ1 ^ q * ρ2 ^ q ), Real.sqrt ( ρ0 ^ q * ρ1 ^ q ), Real.sqrt ( ρ0 ^ q * ρ2 ^ q ), Real.sqrt ( ρ1 ^ q * ρ2 ^ q ), _, _, _, _, _ ⟩ <;> norm_num;
        · refine' div_nonneg _ ( Real.sqrt_nonneg _ );
          have := @Real.add_rpow_le_rpow_add;
          linarith [ this hρ0 hρ1 hq1 ];
        · refine' div_le_one_of_le₀ _ ( Real.sqrt_nonneg _ );
          have := star_inequality hq1 hq ρ0 ρ1 hρ0 hρ1;
          rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] at this;
          rw [ show ρ0 ^ q * ρ1 ^ q = ( ρ0 ^ ( q / 2 ) * ρ1 ^ ( q / 2 ) ) ^ 2 by rw [ mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hρ0, ← Real.rpow_natCast, ← Real.rpow_mul hρ1 ] ; ring_nf, Real.sqrt_sq ( by positivity ) ] ; linarith;
        · refine' div_nonneg _ ( Real.sqrt_nonneg _ );
          have := @Real.add_rpow_le_rpow_add;
          linarith [ this hρ0 hρ2 hq1 ];
        · refine' div_le_one_of_le₀ _ ( Real.sqrt_nonneg _ );
          have := star_inequality hq1 hq ρ0 ρ2 hρ0 hρ2;
          convert sub_le_sub_right this ( ρ0 ^ q + ρ2 ^ q ) using 1 ; ring;
          rw [ Real.sqrt_eq_rpow, ← Real.mul_rpow ( by positivity ) ( by positivity ) ] ; rw [ ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
        · refine' ⟨ _, _, _, _, _ ⟩;
          · refine' div_nonneg _ ( Real.sqrt_nonneg _ );
            have := @Real.add_rpow_le_rpow_add;
            linarith [ this hρ1 hρ2 hq1 ];
          · refine' div_le_one_of_le₀ _ ( Real.sqrt_nonneg _ );
            have := star_inequality hq1 hq ρ1 ρ2 hρ1 hρ2;
            rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] at this;
            rw [ show ρ1 ^ q * ρ2 ^ q = ( ρ1 ^ ( q / 2 ) * ρ2 ^ ( q / 2 ) ) ^ 2 by rw [ mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf ] ; rw [ Real.sqrt_sq ( by positivity ) ] ; linarith;
          · by_cases h : Real.sqrt ( ρ0 ^ q * ρ1 ^ q ) = 0 <;> simp_all +decide [ sub_sub ];
            cases eq_or_ne ρ0 0 <;> cases eq_or_ne ρ1 0 <;> simp_all +decide [ Real.rpow_nonneg ];
            · rw [ Real.zero_rpow ( by positivity ) ];
            · rw [ Real.zero_rpow ( by positivity ) ];
            · exact absurd ( h.resolve_left ( by positivity ) ) ( by positivity );
          · by_cases h : Real.sqrt ( ρ0 ^ q * ρ2 ^ q ) = 0 <;> simp_all +decide [ sub_sub ];
            cases eq_or_ne ρ0 0 <;> cases eq_or_ne ρ2 0 <;> simp_all +decide [ Real.rpow_nonneg ];
            · rw [ Real.zero_rpow ( by positivity ) ];
            · rw [ Real.zero_rpow ( by positivity ) ];
            · exact absurd ( h.resolve_left ( by positivity ) ) ( by positivity );
          · by_cases h : Real.sqrt ( ρ1 ^ q * ρ2 ^ q ) = 0 <;> simp_all +decide [ sub_sub ];
            · simp_all +decide [ Real.rpow_nonneg ];
              cases h <;> simp_all +decide [ Real.rpow_eq_zero_iff_of_nonneg ];
              · rw [ mul_pow, Real.sq_sqrt ( Real.rpow_nonneg hρ0 _ ), Real.sq_sqrt ( Real.rpow_nonneg hρ2 _ ) ];
              · rw [ mul_pow, Real.sq_sqrt ( Real.rpow_nonneg hρ0 _ ), Real.sq_sqrt ( Real.rpow_nonneg hρ1 _ ) ];
            · rw [ Real.sq_sqrt ( by positivity ), Real.sq_sqrt ( by positivity ), Real.sq_sqrt ( by positivity ) ];
              rw [ ← Real.sqrt_mul <| by positivity, ← Real.sqrt_mul <| by positivity ] ; ring_nf;
              exact ⟨ trivial, trivial, trivial, by rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf <;> positivity ⟩;
    -- Apply psd3_of_minors with the given conditions.
    have h_psd : 0 ≤ ρ0 ^ q * ρ1 ^ q - (η01 * hη01 / 2) ^ 2 ∧ 0 ≤ ρ0 ^ q * ρ2 ^ q - (η02 * hη02 / 2) ^ 2 ∧ 0 ≤ ρ1 ^ q * ρ2 ^ q - (η12 * hη12 / 2) ^ 2 ∧ 0 ≤ ρ0 ^ q * ρ1 ^ q * ρ2 ^ q * (1 - (η01 ^ 2 + η02 ^ 2 + η12 ^ 2 + η01 * η02 * η12) / 4) := by
      refine' ⟨ _, _, _, _ ⟩;
      · nlinarith [ show 0 ≤ η01 * hη01 by exact mul_nonneg hS01 ( by linarith ), show η01 * hη01 ≤ 2 * hη01 by nlinarith ];
      · nlinarith [ show 0 ≤ η02 * hη02 by exact mul_nonneg hS12.1 hS12.2.2.2.2.2.1, show η02 * hη02 ≤ 2 * hη02 by nlinarith ];
      · nlinarith [ show 0 ≤ η12 * hη12 by exact mul_nonneg ( by linarith ) ( by linarith ), show η12 * hη12 ≤ 2 * hη12 by exact mul_le_mul_of_nonneg_right ( by linarith ) ( by linarith ) ];
      · refine' mul_nonneg ( mul_nonneg ( mul_nonneg ( Real.rpow_nonneg hρ0 _ ) ( Real.rpow_nonneg hρ1 _ ) ) ( Real.rpow_nonneg hρ2 _ ) ) _;
        exact star_det_nonneg η01 η02 η12 hS01 hS02 hS12.1 hS12.2.1 hS12.2.2.1 hS12.2.2.2.1;
    rw [ h01, h02, h12 ];
    rw [ hS12.2.2.2.2.2.2.2.1, hS12.2.2.2.2.2.2.2.2.1, hS12.2.2.2.2.2.2.2.2.2.1 ];
    convert psd3_of_minors ( ρ0 ^ q ) ( ρ1 ^ q ) ( ρ2 ^ q ) ( - ( η01 * hη01 / 2 ) ) ( - ( η02 * hη02 / 2 ) ) ( - ( η12 * hη12 / 2 ) ) ( by positivity ) ( by positivity ) ( by positivity ) _ _ _ _ a0 a1 a2 using 1 <;> ring_nf;
    · linarith;
    · linarith;
    · linarith;
    · convert h_psd.2.2.2 using 1 ; ring_nf;
      grind

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
  by_cases hu : u1 = u2;
  · grind;
  · unfold schoenDet at *;
    cases lt_or_gt_of_ne hu <;> nlinarith [ mul_le_mul_of_nonneg_left hu1 hC, mul_le_mul_of_nonneg_left hu2 hC, mul_le_mul_of_nonneg_left hu1 ( sub_nonneg.mpr hu2 ), mul_le_mul_of_nonneg_left hu2 ( sub_nonneg.mpr hu1 ) ]

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
  set w := (B + C - d 1 2 ^ q) / 2;
  -- By definition of $A$, $B$, $C$, $u$, $v$, and $w$, we know that $M$ is positive semidefinite.
  have hM_posSemidef : ∀ x y z : ℝ, 0 ≤ A * x ^ 2 + B * y ^ 2 + C * z ^ 2 + 2 * u * x * y + 2 * v * x * z + 2 * w * y * z := by
    intro x y z
    specialize hneg (fun i => if i = 0 then x else if i = 1 then y else if i = 2 then z else -(x + y + z)) (by
    simp +decide [ Fin.sum_univ_four ] ; ring);
    simp +decide [ Fin.sum_univ_four ] at hneg;
    simp_all +decide [ ne_of_gt hq0 ];
    grind;
  -- Since $M$ is positive semidefinite, its determinant is nonnegative.
  have hM_det_nonneg : Matrix.PosSemidef (Matrix.of ![![A, u, v], ![u, B, w], ![v, w, C]]) := by
    constructor;
    · ext i j; fin_cases i <;> fin_cases j <;> rfl;
    · intro x; convert hM_posSemidef ( x 0 ) ( x 1 ) ( x 2 ) using 1; simp +decide [ Finsupp.sum_fintype, Fin.sum_univ_three ] ; ring;
  convert hM_det_nonneg.det_nonneg using 1 ; norm_num [ Matrix.det_fin_three ] ; ring_nf!;
  simp +zetaDelta at *;
  unfold schoenDet; ring;

/-
Negative type is invariant under relabelling the four points.
-/
lemma hasNegType_reindex {q : ℝ} {d : Fin 4 → Fin 4 → ℝ} (σ : Equiv.Perm (Fin 4))
    (h : HasNegType q d) : HasNegType q (fun i j => d (σ i) (σ j)) := by
  intro c hc;
  -- Set c' := fun k => c (σ⁻¹ k).
  set c' : Fin 4 → ℝ := fun k => c (σ⁻¹ k);
  convert h c' _ using 1;
  · convert rfl using 1;
    conv_rhs => rw [ ← Equiv.sum_comp σ⁻¹ ] ;
    exact Finset.sum_congr rfl fun i hi => by rw [ ← Equiv.sum_comp σ ] ; aesop;
  · exact hc ▸ Equiv.sum_comp σ⁻¹ c

/-
**Inversion is a diagonal congruence** of the Schoenberg matrix: scaling row/column
`i` by `Di` multiplies the determinant by `(D0 D1 D2)^2`.
-/
lemma schoenDet_congr (D0 D1 D2 A B C u v w : ℝ) :
    schoenDet (D0 ^ 2 * A) (D1 ^ 2 * B) (D2 ^ 2 * C)
        (D0 * D1 * u) (D0 * D2 * v) (D1 * D2 * w)
      = (D0 * D1 * D2) ^ 2 * schoenDet A B C u v w := by
  unfold schoenDet; ring;

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
  unfold schoenDet; ring

/-- Swapping leaves `1 ↔ 2`. -/
lemma schoenDet_swap12 (A B C u v w : ℝ) :
    schoenDet A C B v u w = schoenDet A B C u v w := by
  unfold schoenDet; ring

/-- Swapping leaves `0 ↔ 2`. -/
lemma schoenDet_swap02 (A B C u v w : ℝ) :
    schoenDet C B A w v u = schoenDet A B C u v w := by
  unfold schoenDet; ring

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
  -- By permutation invariance of $HasNegType$, we can assume without loss of generality that the star has center 3.
  set dS : Fin 4 → Fin 4 → ℝ := fun i j => if i = j then 0 else (if i = 0 then 0 else if i = 1 then r else if i = 2 then z else y) + (if j = 0 then 0 else if j = 1 then r else if j = 2 then z else y);
  -- By permutation invariance, we can assume without loss of generality that the star has center 3.
  set σ : Equiv.Perm (Fin 4) := Equiv.swap 0 3;
  set dS' : Fin 4 → Fin 4 → ℝ := fun i j => dS (σ i) (σ j);
  -- By permutation invariance, we can assume without loss of generality that the star has center 3. Hence, we can apply the star_negType lemma.
  have h_star_negType : HasNegType q dS' := by
    apply star_negType hq1 hq;
    · constructor <;> simp +decide [ dS', dS ];
      simp +decide [ Fin.forall_fin_succ, σ ];
      exact ⟨ ⟨ ⟨ by ring, by ring ⟩, ⟨ by ring, by ring ⟩, by ring, by ring ⟩, ⟨ ⟨ by linarith, by linarith, by linarith ⟩, ⟨ by linarith, by linarith, by linarith ⟩, ⟨ by linarith, by linarith, by linarith ⟩, by linarith, by linarith, by linarith ⟩, ⟨ ⟨ by linarith, by linarith, by linarith ⟩, ⟨ by linarith, by linarith, by linarith ⟩, by linarith ⟩, ⟨ ⟨ by linarith, by linarith, by linarith ⟩, ⟨ by linarith, by linarith, by linarith ⟩, by linarith ⟩, ⟨ ⟨ by linarith, by linarith, by linarith ⟩, ⟨ by linarith, by linarith, by linarith ⟩, by linarith ⟩, ⟨ by linarith, by linarith, by linarith ⟩, ⟨ by linarith, by linarith, by linarith ⟩, by linarith, by linarith, by linarith ⟩;
    · grind;
    · grind;
    · grind;
  convert det_nonneg_of_negType ( show 0 < q by linarith ) dS' _ _ h_star_negType using 1;
  · grind +locals;
  · grind;
  · lia

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
  convert det_nonneg_of_negType hq0 ( fun i j ↦ |( if i = 3 then 0 else if i = 0 then y else if i = 1 then y + r else y + z ) - ( if j = 3 then 0 else if j = 0 then y else if j = 1 then y + r else y + z )| ) _ _ _ using 1 <;> norm_num;
  · simp +decide [ abs_of_nonneg, hy, hr, hz ];
    rw [ abs_of_nonneg ( by positivity : 0 ≤ y + r ), abs_of_nonneg ( by positivity : 0 ≤ y + z ) ];
  · exact fun i j => abs_sub_comm _ _;
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
  apply negType_of_schoenberg (by linarith) d hm.2.1 hm.1 (fun a0 a1 a2 => ?_);
  have := @psd3_of_minors ( d 0 3 ^ q ) ( d 1 3 ^ q ) ( d 2 3 ^ q ) ( ( d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q ) / 2 ) ( ( d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q ) / 2 ) ( ( d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q ) / 2 ) ?_ ?_ ?_ ?_ ?_ ?_ ?_;
  any_goals linarith [ this a0 a1 a2 ];
  all_goals have := hm.2.2.1; simp_all +decide [ Real.rpow_nonneg ];
  any_goals exact Real.rpow_nonneg ( add_nonneg ( this _ _ ) ( this _ _ ) ) _;
  · have := @minor_nonneg q ( by linarith ) ( by linarith [ show Real.logb 2 3 ≤ 2 by rw [ Real.logb_le_iff_le_rpow ] <;> norm_num ] ) ( d 0 3 ) ( d 1 3 ) ( d 0 1 ) ; simp_all +decide;
    exact this ( by linarith [ ‹∀ i j, 0 ≤ d i j› 0 3, ‹∀ i j, 0 ≤ d i j› 0 1 ] ) ( by linarith [ ‹∀ i j, 0 ≤ d i j› 0 3, ‹∀ i j, 0 ≤ d i j› 0 1 ] ) ( by linarith [ ‹∀ i j, 0 ≤ d i j› 0 3, ‹∀ i j, 0 ≤ d i j› 0 1 ] ) ( by linarith [ ‹∀ i j, 0 ≤ d i j› 0 3, ‹∀ i j, 0 ≤ d i j› 0 1 ] );
  · have := @minor_nonneg q ( by linarith ) ( by linarith [ show Real.logb 2 3 ≤ 2 by rw [ Real.logb_le_iff_le_rpow ] <;> norm_num ] ) ( d 0 3 ) ( d 0 3 + d 0 2 ) ( d 0 2 ) ( this _ _ ) ( add_nonneg ( this _ _ ) ( this _ _ ) ) ( this _ _ ) ?_ ?_ ?_ <;> norm_num at *;
    · linarith;
    · linarith [ this 0 3, this 0 2 ];
    · linarith [ this 0 2, this 0 3 ];
    · linarith;
  · have := @minor_nonneg q ( by linarith ) ( by linarith [ show Real.logb 2 3 ≤ 2 by rw [ Real.logb_le_iff_le_rpow ] <;> norm_num ] ) ( d 0 3 + d 0 1 ) ( d 0 3 + d 0 2 ) ( d 1 2 ) ?_ ?_ ?_ ?_ ?_ ?_ <;> try linarith [ this 0 3, this 0 1, this 0 2, this 1 2 ];
    · linarith;
    · linarith [ hm.2.2.2 1 0 2, hm.2.2.2 2 0 1, hm.2.2.2 1 3 2, hm.2.2.2 2 3 1, hm.2.1 1 3, hm.2.1 2 3 ];
    · linarith [ hm.2.2.2 0 1 2, hm.2.2.2 0 2 1, hm.2.2.2 1 2 0, hm.2.2.2 1 0 2, hm.2.2.2 2 0 1, hm.2.2.2 2 1 0, hm.2.1 0 1, hm.2.1 0 2, hm.2.1 1 2 ];
    · linarith [ hm.2.2.2 0 1 2, hm.2.2.2 0 2 1, hm.2.2.2 1 2 0, hm.2.2.2 1 0 2, hm.2.2.2 2 0 1, hm.2.2.2 2 1 0, hm.2.1 0 1, hm.2.1 0 2, hm.2.1 1 2 ];
  · have h_det_nonneg : 0 ≤ schoenDet (d 2 3 ^ q) (d 1 3 ^ q) (d 0 3 ^ q) (((d 2 3 ^ q + d 1 3 ^ q - d 1 2 ^ q) / 2)) (((d 2 3 ^ q + d 0 3 ^ q - d 0 2 ^ q) / 2)) (((d 1 3 ^ q + d 0 3 ^ q - d 0 1 ^ q) / 2)) := by
      apply schoenDet_ge_of_endpoints;
      exact Real.rpow_nonneg ( this _ _ ) _;
      rotate_left;
      rotate_left;
      rotate_left;
      rotate_left;
      exact ( ( d 0 3 + d 0 2 ) ^ q + ( d 0 3 + d 0 1 ) ^ q - ( d 0 1 + d 0 2 ) ^ q ) / 2;
      exact ( ( d 0 3 + d 0 2 ) ^ q + ( d 0 3 + d 0 1 ) ^ q - |d 0 1 - d 0 2| ^ q ) / 2;
      · rw [ hU, hV ];
        gcongr;
        · exact this _ _;
        · exact hm.2.2.2 1 0 2 |> le_trans <| by linarith [ hm.2.1 0 1, hm.2.1 0 2 ] ;
      · gcongr;
        · exact this _ _;
        · linarith;
        · exact this _ _;
        · linarith;
        · have := hm.2.2.2 0 1 2; ( have := hm.2.2.2 0 2 1; ( norm_num at *; cases abs_cases ( d 0 1 - d 0 2 ) <;> linarith! [ this, hm.2.1 0 1, hm.2.1 0 2, hm.2.1 1 2 ] ; ) );
      · convert endpoint_star_det hq1 hq ( d 0 3 ) ( d 0 2 ) ( d 0 1 ) ( this _ _ ) ( this _ _ ) ( this _ _ ) using 1 ; ring_nf;
        unfold schoenDet; ring_nf;
        grind +qlia;
      · convert endpoint_line_det ( show 0 < q by linarith ) ( show q ≤ 2 by linarith [ show Real.logb 2 3 ≤ 2 by rw [ Real.logb_le_iff_le_rpow ] <;> norm_num ] ) ( d 0 3 ) ( d 0 1 ) ( d 0 2 ) ( this _ _ ) ( this _ _ ) ( this _ _ ) using 1;
        unfold schoenDet; ring_nf;
        rw [ hU, hV ] ; ring;
    unfold schoenDet at h_det_nonneg; rw [ hU, hV ] at h_det_nonneg; linarith;

/-
**Metric-inversion (Ptolemy-equality) endpoint.**  With apex `A = 3`, `P = 1`
on the geodesic `A`–`B = 2`, all apex distances positive, and the Ptolemy bound
holding with equality, the Schoenberg determinant based at `3` is nonnegative.
Proof: invert the metric at `A`; the inverted metric is an attached-ray
configuration, so its determinant is `≥ 0` by `attached_ray_negType`, and by the
diagonal-congruence identity `schoenDet_congr` the original determinant is a
positive multiple of it.
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
  -- Define the inverted metric `dh`.
  set dh : Fin 4 → Fin 4 → ℝ := fun i j =>
    if i = j then 0
    else if i = 3 then 1 / d j 3
    else if j = 3 then 1 / d i 3
    else d i j / (d i 3 * d j 3);
  -- Prove that `dh` is a metric.
  have hdh_metric : IsMetric4 dh := by
    refine' ⟨ _, _, _, _ ⟩;
    · aesop;
    · simp +decide [ dh, hm.2.1 ];
      grind;
    · intro i j; fin_cases i <;> fin_cases j <;> simp +decide [ * ] ;
      all_goals simp +decide [ dh, hm.2.2.1 ];
      all_goals exact div_nonneg ( hm.2.2.1 _ _ ) ( mul_nonneg ( hm.2.2.1 _ _ ) ( hm.2.2.1 _ _ ) ) ;
    · intro i j k;
      by_cases hi : i = 3 <;> by_cases hj : j = 3 <;> by_cases hk : k = 3 <;> simp +decide [ hi, hj, hk, dh ];
      · split_ifs <;> linarith [ inv_nonneg.2 ( show 0 ≤ d j 3 by exact hm.2.2.1 _ _ ) ];
      · split_ifs <;> simp_all +decide [ div_eq_mul_inv ];
        field_simp;
        rw [ div_le_div_iff₀ ];
        · rw [ add_mul, div_mul_cancel₀ ] <;> norm_num;
          · grind +locals;
          · fin_cases k <;> simp_all +decide [ IsMetric4 ]; all_goals linarith;
        · fin_cases k <;> simp_all +decide [ hm.2.1 ];
        · grind;
      · split_ifs <;> simp_all +decide [ div_eq_mul_inv ];
        · exact hm.2.2.1 _ _;
        · have := hm.2.2.2 i 3 k;
          field_simp;
          rw [ div_add_div, div_le_div_iff₀ ];
          · convert mul_le_mul_of_nonneg_right this ( mul_nonneg ( hm.2.2.1 i 3 ) ( hm.2.2.1 k 3 ) ) using 1 ; ring_nf;
            rw [ hm.2.1 ] ; ring;
          · fin_cases i <;> fin_cases k <;> simp_all +decide;
          · fin_cases i <;> fin_cases k <;> simp_all +decide;
          · grind +splitIndPred;
          · grind;
      · split_ifs <;> simp_all +decide [ div_eq_mul_inv, mul_comm ];
        field_simp;
        rw [ div_add_one, div_div, div_le_div_iff₀ ];
        · have := hm.2.2.2 j i 3; simp_all +decide [ hm.2.1 ] ;
          nlinarith [ hm.2.2.1 i 3, hm.2.2.1 j 3 ];
        · fin_cases i <;> fin_cases j <;> simp_all +decide;
        · fin_cases i <;> fin_cases j <;> simp +decide [ * ] at *;
        · grind +splitIndPred;
      · split_ifs <;> simp_all +decide [ mul_comm ];
        · exact add_nonneg ( div_nonneg ( hm.2.2.1 _ _ ) ( mul_nonneg ( hm.2.2.1 _ _ ) ( hm.2.2.1 _ _ ) ) ) ( div_nonneg ( hm.2.2.1 _ _ ) ( mul_nonneg ( hm.2.2.1 _ _ ) ( hm.2.2.1 _ _ ) ) );
        · rw [ div_add_div, div_le_div_iff₀ ];
          · have := hp i k j 3;
            convert mul_le_mul_of_nonneg_right this ( show 0 ≤ d i 3 * d j 3 * d k 3 by exact mul_nonneg ( mul_nonneg ( hm.2.2.1 _ _ ) ( hm.2.2.1 _ _ ) ) ( hm.2.2.1 _ _ ) ) using 1 <;> ring_nf;
            rw [ hm.2.1 j k ];
          · fin_cases i <;> fin_cases k <;> simp_all +decide;
          · fin_cases i <;> fin_cases j <;> fin_cases k <;> simp +decide at hi hj hk ‹¬_› ‹¬_› ‹¬_› ⊢ <;> positivity;
          · fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all +decide;
            all_goals constructor <;> linarith;
          · fin_cases j <;> fin_cases k <;> simp_all +decide [ ne_of_gt ];
  -- Prove that `dh` has `q`-negative type.
  have hdh_negType : HasNegType q dh := by
    -- Apply the attached-ray lemma to `dh`.
    have hdh_attached_ray : HasNegType q (fun i j => dh (Equiv.swap 0 2 (Equiv.swap 1 3 i)) (Equiv.swap 0 2 (Equiv.swap 1 3 j))) := by
      apply attached_ray_negType hq1 hq;
      · exact ⟨ fun i => hdh_metric.1 _, fun i j => hdh_metric.2.1 _ _, fun i j => hdh_metric.2.2.1 _ _, fun i j k => hdh_metric.2.2.2 _ _ _ ⟩;
      · simp +decide [ dh, Equiv.swap_apply_def ];
        field_simp;
        linarith [ hm.2.1 3 2, hm.2.1 3 1, hm.2.1 2 1 ];
      · simp +decide [ dh, Equiv.swap_apply_def ];
        grind +locals;
    convert hasNegType_reindex ( Equiv.swap 0 2 * Equiv.swap 1 3 )⁻¹ hdh_attached_ray using 1;
    exact funext fun i => funext fun j => by fin_cases i <;> fin_cases j <;> rfl;
  have h_det_eq : schoenDet (dh 0 3 ^ q) (dh 1 3 ^ q) (dh 2 3 ^ q) ((dh 0 3 ^ q + dh 1 3 ^ q - dh 0 1 ^ q) / 2) ((dh 0 3 ^ q + dh 2 3 ^ q - dh 0 2 ^ q) / 2) ((dh 1 3 ^ q + dh 2 3 ^ q - dh 1 2 ^ q) / 2) = (d 0 3 ^ (-q) * d 1 3 ^ (-q) * d 2 3 ^ (-q)) ^ 2 * schoenDet (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q) ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2) ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2) ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2) := by
    convert schoenDet_congr ( d 0 3 ^ ( -q ) ) ( d 1 3 ^ ( -q ) ) ( d 2 3 ^ ( -q ) ) ( d 0 3 ^ q ) ( d 1 3 ^ q ) ( d 2 3 ^ q ) ( ( d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q ) / 2 ) ( ( d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q ) / 2 ) ( ( d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q ) / 2 ) using 1;
    simp +zetaDelta at *;
    norm_num [ Real.rpow_neg hpos0.le, Real.rpow_neg hpos1.le, Real.rpow_neg hpos2.le, Real.div_rpow ( show 0 ≤ d 0 1 by exact hm.2.2.1 _ _ ) ( show 0 ≤ d 0 3 * d 1 3 by positivity ), Real.div_rpow ( show 0 ≤ d 0 2 by exact hm.2.2.1 _ _ ) ( show 0 ≤ d 0 3 * d 2 3 by positivity ), Real.div_rpow ( show 0 ≤ d 1 2 by exact hm.2.2.1 _ _ ) ( show 0 ≤ d 1 3 * d 2 3 by positivity ) ];
    norm_num [ Real.inv_rpow ( le_of_lt hpos0 ), Real.inv_rpow ( le_of_lt hpos1 ), Real.inv_rpow ( le_of_lt hpos2 ), Real.mul_rpow ( le_of_lt hpos0 ) ( le_of_lt hpos1 ), Real.mul_rpow ( le_of_lt hpos0 ) ( le_of_lt hpos2 ), Real.mul_rpow ( le_of_lt hpos1 ) ( le_of_lt hpos2 ) ];
    field_simp;
    ring_nf;
  contrapose! h_det_eq;
  refine' ne_of_gt ( lt_of_lt_of_le _ ( det_nonneg_of_negType ( by positivity ) dh _ _ hdh_negType ) );
  · exact mul_neg_of_pos_of_neg ( sq_pos_of_pos ( mul_pos ( mul_pos ( Real.rpow_pos_of_pos hpos0 _ ) ( Real.rpow_pos_of_pos hpos1 _ ) ) ( Real.rpow_pos_of_pos hpos2 _ ) ) ) h_det_eq;
  · exact hdh_metric.2.1;
  · exact fun i => hdh_metric.1 i

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
  -- Main case: all three apex distances are strictly positive.
  have hA' : 0 < d 0 3 := lt_of_le_of_ne (hnn 0 3) (Ne.symm hA)
  have hB' : 0 < d 1 3 := lt_of_le_of_ne (hnn 1 3) (Ne.symm hB)
  have hC' : 0 < d 2 3 := lt_of_le_of_ne (hnn 2 3) (Ne.symm hC)
  -- Fold the goal into canonical `schoenDet` form, ready for the concavity
  -- reduction (`schoenDet_ge_of_endpoints`) and leaf-permutation lemmas.
  suffices h : 0 ≤ schoenDet (d 0 3 ^ q) (d 1 3 ^ q) (d 2 3 ^ q)
      ((d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q) / 2)
      ((d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q) / 2)
      ((d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q) / 2) by
    unfold schoenDet at h; linarith
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
    · rw [abs_le]; exact ⟨by linarith [htri 1 0 3, hsymm 1 0], by linarith [htri 0 1 3]⟩
    · rw [abs_le]; exact ⟨by linarith [htri 1 0 2, hsymm 1 0], by linarith [htri 0 1 2]⟩
    · rw [div_le_iff₀ hC', abs_le]
      have ha := hp 0 3 1 2; rw [hsymm 3 2, hsymm 3 1] at ha
      have hb := hp 0 2 1 3; rw [hsymm 2 1] at hb
      exact ⟨by linarith [ha], by linarith [hb]⟩
  · -- `d 0 1 ≤ t2` : `d 0 1` is below every upper bound
    refine le_min (le_min ?_ ?_) ?_
    · linarith [htri 0 3 1, hsymm 3 1]
    · linarith [htri 0 2 1, hsymm 2 1]
    · rw [le_div_iff₀ hC']; linarith [hp 0 1 2 3]
  · -- endpoint `t1` (lower): the tightest lower bound is active.
    rcases max_cases (max |d 0 3 - d 1 3| |d 0 2 - d 1 2|) (|d 0 2 * d 1 3 - d 0 3 * d 1 2| / d 2 3)
      with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
      rcases max_cases |d 0 3 - d 1 3| |d 0 2 - d 1 2| with ⟨he2, _⟩ | ⟨he2, _⟩
      · rw [he2]
        -- `d 0 1 = |d03 - d13|`: leaf 0 or apex 3 is collinear with the {0,1,3} triangle.
        sorry
      · rw [he2]
        -- `d 0 1 = |d02 - d12|`: collinearity in the {0,1,2} triangle.
        sorry
    · rw [he]
      -- `d 0 1` at the lower Ptolemy bound.
      sorry
  · -- endpoint `t2` (upper): the tightest upper bound is active.
    rcases min_cases (min (d 0 3 + d 1 3) (d 0 2 + d 1 2)) ((d 0 2 * d 1 3 + d 0 3 * d 1 2) / d 2 3)
      with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
      rcases min_cases (d 0 3 + d 1 3) (d 0 2 + d 1 2) with ⟨he2, _⟩ | ⟨he2, _⟩
      · rw [he2]
        -- `d 0 1 = d03 + d13`: apex 3 lies between leaves 0 and 1 (geodesic insertion).
        sorry
      · rw [he2]
        -- `d 0 1 = d02 + d12`: leaf 2 lies between leaves 0 and 1 (geodesic insertion).
        sorry
    · rw [he]
      -- `d 0 1` at the upper Ptolemy bound: Ptolemy equality.
      sorry

/-
**Negative type for `1 ≤ q ≤ log₂ 3`** via the positive semidefinite Schoenberg
matrix.
-/
lemma negType_ge_one {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ Real.logb 2 3)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) (hp : IsPtolemaic4 d) :
    HasNegType q d := by
  convert negType_of_schoenberg ( by linarith : 0 < q ) d hm.2.1 hm.1 ( fun a0 a1 a2 => ?_ ) using 1;
  have := @psd3_of_minors ( d 0 3 ^ q ) ( d 1 3 ^ q ) ( d 2 3 ^ q ) ( ( d 0 3 ^ q + d 1 3 ^ q - d 0 1 ^ q ) / 2 ) ( ( d 0 3 ^ q + d 2 3 ^ q - d 0 2 ^ q ) / 2 ) ( ( d 1 3 ^ q + d 2 3 ^ q - d 1 2 ^ q ) / 2 ) ?_ ?_ ?_ ?_ ?_ ?_ ?_;
  any_goals exact Real.rpow_nonneg ( hm.2.2.1 _ _ ) _;
  · linarith [ this a0 a1 a2 ];
  · convert minor_nonneg ( show 0 < q by positivity ) ( show q ≤ 2 by linarith [ show Real.logb 2 3 < 2 by rw [ Real.logb_lt_iff_lt_rpow ] <;> norm_num ] ) ( d 0 3 ) ( d 1 3 ) ( d 0 1 ) ( hm.2.2.1 _ _ ) ( hm.2.2.1 _ _ ) ( hm.2.2.1 _ _ ) _ _ _ using 1 <;> ring_nf;
    · simpa only [ hm.2.1 ] using hm.2.2.2 0 3 1;
    · exact hm.2.2.2 _ _ _;
    · linarith [ hm.2.2.2 1 0 3, hm.2.1 0 1 ];
  · convert minor_nonneg ( by linarith : 0 < q ) ( by linarith [ show Real.logb 2 3 < 2 by rw [ Real.logb_lt_iff_lt_rpow ] <;> norm_num ] : q ≤ 2 ) ( d 0 3 ) ( d 2 3 ) ( d 0 2 ) ( hm.2.2.1 _ _ ) ( hm.2.2.1 _ _ ) ( hm.2.2.1 _ _ ) _ _ _ using 1;
    · simpa only [ hm.2.1 _ 3 ] using hm.2.2.2 0 3 2;
    · exact hm.2.2.2 _ _ _;
    · simpa only [ hm.2.1 ] using hm.2.2.2 2 0 3;
  · convert minor_nonneg ( show 0 < q by positivity ) ( show q ≤ 2 by linarith [ show Real.logb 2 3 < 2 by rw [ Real.logb_lt_iff_lt_rpow ] <;> norm_num ] ) ( d 1 3 ) ( d 2 3 ) ( d 1 2 ) ( hm.2.2.1 _ _ ) ( hm.2.2.1 _ _ ) ( hm.2.2.1 _ _ ) _ _ _ using 1 <;> ring_nf;
    · simpa only [ hm.2.1 ] using hm.2.2.2 1 3 2;
    · exact hm.2.2.2 _ _ _;
    · exact hm.2.2.2 2 1 3 |> le_trans <| by rw [ hm.2.1 ] ;
  · convert schoenberg_det_nonneg hq1 hq d hm hp using 1

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
  rcases le_total g01 g02 with h12 | h12
  · rcases le_total g01 g12 with h13 | h13
    · have hA : (0:ℝ) ≤ r0 - g02 := by linarith
      have hB : (0:ℝ) ≤ r1 - g12 := by linarith
      have hC : (0:ℝ) ≤ r2 - (g02 + g12 - g01) := by linarith
      have hD : (0:ℝ) ≤ g02 - g01 := by linarith
      have hE : (0:ℝ) ≤ g12 - g01 := by linarith
      nlinarith [mul_nonneg (mul_nonneg hA hB) hC, mul_nonneg (mul_nonneg hA hB) hD, mul_nonneg (mul_nonneg hA hB) hE, mul_nonneg (mul_nonneg hA hB) hg01, mul_nonneg (mul_nonneg hA hC) hD, mul_nonneg (mul_nonneg hA hC) hE, mul_nonneg (mul_nonneg hA hC) hg01, mul_nonneg (mul_nonneg hA hD) hE, mul_nonneg (mul_nonneg hA hD) hg01, mul_nonneg (mul_nonneg hA hE) hg01, mul_nonneg (mul_nonneg hB hC) hD, mul_nonneg (mul_nonneg hB hC) hE, mul_nonneg (mul_nonneg hB hC) hg01, mul_nonneg (mul_nonneg hB hD) hE, mul_nonneg (mul_nonneg hB hD) hg01, mul_nonneg (mul_nonneg hB hE) hg01, mul_nonneg (mul_nonneg hC hD) hE, mul_nonneg (mul_nonneg hC hD) hg01, mul_nonneg (mul_nonneg hC hE) hg01, mul_nonneg (mul_nonneg hD hE) hg01]
    · have hA : (0:ℝ) ≤ r0 - (g01 + g02 - g12) := by linarith
      have hB : (0:ℝ) ≤ r1 - g01 := by linarith
      have hC : (0:ℝ) ≤ r2 - g02 := by linarith
      have hD : (0:ℝ) ≤ g01 - g12 := by linarith
      have hE : (0:ℝ) ≤ g02 - g12 := by linarith
      nlinarith [mul_nonneg (mul_nonneg hA hB) hC, mul_nonneg (mul_nonneg hA hB) hD, mul_nonneg (mul_nonneg hA hB) hE, mul_nonneg (mul_nonneg hA hB) hg12, mul_nonneg (mul_nonneg hA hC) hD, mul_nonneg (mul_nonneg hA hC) hE, mul_nonneg (mul_nonneg hA hC) hg12, mul_nonneg (mul_nonneg hA hD) hE, mul_nonneg (mul_nonneg hA hD) hg12, mul_nonneg (mul_nonneg hA hE) hg12, mul_nonneg (mul_nonneg hB hC) hD, mul_nonneg (mul_nonneg hB hC) hE, mul_nonneg (mul_nonneg hB hC) hg12, mul_nonneg (mul_nonneg hB hD) hE, mul_nonneg (mul_nonneg hB hD) hg12, mul_nonneg (mul_nonneg hB hE) hg12, mul_nonneg (mul_nonneg hC hD) hE, mul_nonneg (mul_nonneg hC hD) hg12, mul_nonneg (mul_nonneg hC hE) hg12, mul_nonneg (mul_nonneg hD hE) hg12]
  · rcases le_total g02 g12 with h23 | h23
    · have hA : (0:ℝ) ≤ r0 - g01 := by linarith
      have hB : (0:ℝ) ≤ r1 - (g01 + g12 - g02) := by linarith
      have hC : (0:ℝ) ≤ r2 - g12 := by linarith
      have hD : (0:ℝ) ≤ g01 - g02 := by linarith
      have hE : (0:ℝ) ≤ g12 - g02 := by linarith
      nlinarith [mul_nonneg (mul_nonneg hA hB) hC, mul_nonneg (mul_nonneg hA hB) hD, mul_nonneg (mul_nonneg hA hB) hE, mul_nonneg (mul_nonneg hA hB) hg02, mul_nonneg (mul_nonneg hA hC) hD, mul_nonneg (mul_nonneg hA hC) hE, mul_nonneg (mul_nonneg hA hC) hg02, mul_nonneg (mul_nonneg hA hD) hE, mul_nonneg (mul_nonneg hA hD) hg02, mul_nonneg (mul_nonneg hA hE) hg02, mul_nonneg (mul_nonneg hB hC) hD, mul_nonneg (mul_nonneg hB hC) hE, mul_nonneg (mul_nonneg hB hC) hg02, mul_nonneg (mul_nonneg hB hD) hE, mul_nonneg (mul_nonneg hB hD) hg02, mul_nonneg (mul_nonneg hB hE) hg02, mul_nonneg (mul_nonneg hC hD) hE, mul_nonneg (mul_nonneg hC hD) hg02, mul_nonneg (mul_nonneg hC hE) hg02, mul_nonneg (mul_nonneg hD hE) hg02]
    · have hA : (0:ℝ) ≤ r0 - (g01 + g02 - g12) := by linarith
      have hB : (0:ℝ) ≤ r1 - g01 := by linarith
      have hC : (0:ℝ) ≤ r2 - g02 := by linarith
      have hD : (0:ℝ) ≤ g01 - g12 := by linarith
      have hE : (0:ℝ) ≤ g02 - g12 := by linarith
      nlinarith [mul_nonneg (mul_nonneg hA hB) hC, mul_nonneg (mul_nonneg hA hB) hD, mul_nonneg (mul_nonneg hA hB) hE, mul_nonneg (mul_nonneg hA hB) hg12, mul_nonneg (mul_nonneg hA hC) hD, mul_nonneg (mul_nonneg hA hC) hE, mul_nonneg (mul_nonneg hA hC) hg12, mul_nonneg (mul_nonneg hA hD) hE, mul_nonneg (mul_nonneg hA hD) hg12, mul_nonneg (mul_nonneg hA hE) hg12, mul_nonneg (mul_nonneg hB hC) hD, mul_nonneg (mul_nonneg hB hC) hE, mul_nonneg (mul_nonneg hB hC) hg12, mul_nonneg (mul_nonneg hB hD) hE, mul_nonneg (mul_nonneg hB hD) hg12, mul_nonneg (mul_nonneg hB hE) hg12, mul_nonneg (mul_nonneg hC hD) hE, mul_nonneg (mul_nonneg hC hD) hg12, mul_nonneg (mul_nonneg hC hE) hg12, mul_nonneg (mul_nonneg hD hE) hg12]

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
  apply negType_of_schoenberg one_pos d hm.2.1 hm.1
  intro a0 a1 a2
  have hmn := hm.2.2.1
  have hkey := psd3_of_minors (d 0 3) (d 1 3) (d 2 3)
    ((d 0 3 + d 1 3 - d 0 1) / 2) ((d 0 3 + d 2 3 - d 0 2) / 2)
    ((d 1 3 + d 2 3 - d 1 2) / 2)
    (hmn 0 3) (hmn 1 3) (hmn 2 3) ?_ ?_ ?_ ?_ a0 a1 a2
  · simp only [Real.rpow_one]; nlinarith [hkey]
  · have := minor_nonneg (q := 1) one_pos (by norm_num) (d 0 3) (d 1 3) (d 0 1)
      (hmn 0 3) (hmn 1 3) (hmn 0 1)
      (by simpa [hm.2.1] using hm.2.2.2 0 3 1) (hm.2.2.2 0 1 3)
      (by simpa [hm.2.1] using hm.2.2.2 1 0 3)
    simpa only [Real.rpow_one] using this
  · have := minor_nonneg (q := 1) one_pos (by norm_num) (d 0 3) (d 2 3) (d 0 2)
      (hmn 0 3) (hmn 2 3) (hmn 0 2)
      (by simpa [hm.2.1] using hm.2.2.2 0 3 2) (hm.2.2.2 0 2 3)
      (by simpa [hm.2.1] using hm.2.2.2 2 0 3)
    simpa only [Real.rpow_one] using this
  · have := minor_nonneg (q := 1) one_pos (by norm_num) (d 1 3) (d 2 3) (d 1 2)
      (hmn 1 3) (hmn 2 3) (hmn 1 2)
      (by simpa [hm.2.1] using hm.2.2.2 1 3 2) (hm.2.2.2 1 2 3)
      (by simpa [hm.2.1] using hm.2.2.2 2 1 3)
    simpa only [Real.rpow_one] using this
  · have := metric4_det_q1_nonneg d hm
    simpa only [Real.rpow_one, schoenDet] using this

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
  simp [Fin.sum_univ_four] at hle ⊢;
  simp +zetaDelta at *;
  simp_all +decide [ Fin.sum_univ_four, IsMetric4 ] ; nlinarith! [ sq_nonneg ( a 0 + a 1 + a 2 + a 3 ) ] ;

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
      intro i j; simp only []; rw [hm.2.1 j i]; ring
    have hrelB : ∀ i j : Fin 4, d i j
        = (fun i j => (d i 3 + d j 3 - d i j) / 2) i i
        + (fun i j => (d i 3 + d j 3 - d i j) / 2) j j
        - 2 * (fun i j => (d i 3 + d j 3 - d i j) / 2) i j := by
      intro i j; simp only []; rw [hm.1 i, hm.1 j]; ring
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
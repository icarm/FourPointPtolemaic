# Summary of changes for run c3e404b6-0c40-4e08-99ab-66188dfd44dd
## What I did

I continued the four-point Ptolemaic snowflake formalization, eliminating one of the two remaining `sorry`s and building the supporting theory for it from scratch.

### Blumenthal's theorem (`0 < q ≤ 1`) — now fully proved
`blumenthal_negType` in `RequestProject/Ptolemaic.lean` (every four-point metric has `q`-negative type for `0 < q ≤ 1`) is now complete with **no `sorry`** and only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

To do this I built a new self-contained file `RequestProject/ExpKernel.lean` developing the conditionally-negative-type / Schoenberg kernel machinery (which Mathlib does not provide), all proven with no `sorry`:
- `QPos` (nonnegative quadratic form) with the bridge to `Matrix.PosSemidef`;
- the **Schur product theorem** (`QPos.mul`), **Schur powers** (`QPos.pow`), and the **exponential kernel** (`QPos.exp`);
- the **Gaussian / negative-distance kernel** `exp(-(t·d))` positivity (`qpos_exp_neg_dist`);
- the **resolvent kernel** `1/(t+d)` positivity (`qpos_resolvent`);
- the **downward-closure theorem** `qpos_downward` (if `d` is conditionally-negative-type then `d^p` is too, for `0 < p < 1`), via Mathlib's integral representation of `x^p`.

In `Ptolemaic.lean` I added the lemmas that feed this: `det_gromov_nonneg` (an explicit cut/Gromov-product decomposition certificate), `metric4_det_q1_nonneg` (every four-point metric has nonnegative Schoenberg determinant at `q=1`), `metric4_one_negType` (every four-point metric has `1`-negative type), and `metric4_qpos_gram`, then assembled `blumenthal_negType` (using `1`-negative type directly for `q=1` and downward closure for `q<1`).

### What remains
The single remaining `sorry` is `schoenberg_det_nonneg` (the determinant nonnegativity for the Ptolemaic range `1 ≤ q ≤ log₂ 3`). This is the paper's hardest step — a variational negative-minimizer / active-constraint polytope argument. All of its supporting machinery (concavity, the star/line/geodesic endpoint lemmas, metric inversion) was already proved by earlier work; what remains is the large combinatorial assembly, which I judged too large to complete reliably this session without risking unproven scaffolding. The main theorem `four_point_ptolemaic_negType` is assembled from it and so still depends on this one `sorry`.

### Status
- `RequestProject/Main.lean` (the original result: finite subsets of ℝ have `q`-negative type for `0 < q ≤ 2`): unchanged, complete.
- `RequestProject/ExpKernel.lean`: new, entirely `sorry`-free, axiom-clean.
- `RequestProject/Ptolemaic.lean`: Blumenthal range now complete; one `sorry` remains (`schoenberg_det_nonneg`).
- The whole project builds successfully. `PTOLEMAIC_STATUS.md` is updated to reflect this progress (I left `ARISTOTLE_SUMMARY.md` untouched as requested).

# Summary of changes for run c2d25e6f-a212-4146-bfb7-24b07048953e
## What was requested

Prove `thm:q5-four-point-ptolemaic` from `part2_sandwiches.tex`: *every four-point Ptolemaic metric has `q`-negative type for `0 < q ≤ log₂ 3`*, reusing the previously-proved line-metric result.

## Honest status

The theorem is **formalized faithfully and reduced to two documented lemmas, but is not yet fully proved** — two deep components remain as `sorry`. All other supporting mathematics (the bulk of the paper's argument, including its hardest analytic and geometric steps) is fully verified. The original project result (finite subsets of ℝ have `q`-negative type for `0 < q ≤ 2`, in `RequestProject/Main.lean`) is unchanged and complete.

New work is in `RequestProject/Ptolemaic.lean` (imports `RequestProject/Main.lean`); a precise breakdown is in `PTOLEMAIC_STATUS.md`.

## Faithful statement

`four_point_ptolemaic_negType {q} (hq0 : 0 < q) (hq : q ≤ Real.logb 2 3) (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) (hp : IsPtolemaic4 d) : HasNegType q d`, with `IsMetric4`, `IsPtolemaic4`, `HasNegType` the standard four-point definitions.

## Fully proved (no `sorry`; axioms only `propext`, `Classical.choice`, `Quot.sound`)

- Schoenberg's criterion both directions (`negType_of_schoenberg`, `det_nonneg_of_negType`), the algebraic PSD fact `psd3_of_minors`, and one-entry concavity `schoenDet_ge_of_endpoints`.
- The **star inequality** `(a+b)^q ≤ a^q+b^q+(ab)^{q/2}` in full, including its genuine calculus core (`theta_nonneg`, `psi_key`, `star_single_p0`, …) — the step where `log₂ 3` enters.
- `2×2` minor nonnegativity `minor_nonneg`; **line metrics** `line_negType` (transporting the requested `NegType.real_finite_negative_type` to `Fin 4`); **star metrics** `star_negType`.
- Relabelling invariance `hasNegType_reindex`; **metric inversion as a diagonal congruence** `schoenDet_congr`.
- The **attached-ray extension** `attached_ray_negType` (with its endpoint determinants), and the **metric-inversion / Ptolemy-equality endpoint** `geodesic_ptolemy_endpoint_det` — the crux step of the geodesic-insertion lemma, combining inversion, the attached-ray lemma and relabelling.

## What remains (the two `sorry`s)

- `schoenberg_det_nonneg`: the determinant case-analysis. Every mechanism it needs is proved above; what remains is the combinatorial assembly — reduce each off-diagonal Schoenberg entry to its feasible-interval endpoints by concavity, each endpoint being a geodesic-insertion configuration discharged by the attached-ray / line / star / inversion lemmas (after relabelling), with the polytope feasibility bookkeeping.
- `blumenthal_negType`: the classical range `0 < q ≤ 1`, obtainable from the `q = 1` case by downward closure of negative type.

The project builds successfully (the new file compiles with exactly these two `sorry`s; everything else is verified). I was not able to complete the final determinant assembly and the `q ≤ 1` case within this session.

# Summary of changes for run 834cf8f4-5d17-4bf8-ada9-f625e228d4d0
I proved that every finite subset of the reals, with the usual metric, has q-negative type for 0 < q ≤ 2.

## Result

In `RequestProject/Main.lean`, the main theorem `NegType.real_finite_negative_type` states: for `0 < q ≤ 2`, any finite set `S : Finset ℝ`, and any weights `c : ℝ → ℝ` with `∑ x ∈ S, c x = 0`,
```
∑ x ∈ S, ∑ y ∈ S, c x * c y * |x - y| ^ q ≤ 0.
```
This is exactly the defining inequality of q-negative type for the finite subset `S ⊆ ℝ` with metric `d x y = |x - y|` (the quadratic form of the q-th power of the distance is nonpositive on weight vectors summing to zero).

The build is clean: it compiles with no `sorry`/`axiom`/`@[implemented_by]`, and `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`. (One cosmetic linter note remains on a load-bearing reverse-rewrite `simp` argument that the linter misreports as unused; removing it breaks the proof.)

## Proof structure

The argument splits at the endpoint:

- **0 < q < 2 (`neg_type_lt_two`)** uses the integral representation
  `|t|^q = (1/K) ∫_(0,∞) (1 − cos(t s)) / s^(1+q) ds`, where `K = ∫_(0,∞) (1 − cos s)/s^(1+q) ds`. Supporting lemmas:
  - `integrable_kern` / `integrable_g`: integrability of the kernel on `(0,∞)`, via a near-0 bound `1 − cos ≤ (ts)²/2` (giving an `s^(1−q)` comparison, integrable since `q < 2`) and a near-∞ bound `≤ 2 s^(−(1+q))` (integrable since `q > 0`);
  - `integral_kern_eq`: the scaling identity, proved by a change of variables and evenness of cosine;
  - `Kconst_pos`: `K > 0`, since the integrand is nonnegative and positive on a set of positive measure;
  - `pointwise_nonpos`: the pointwise identity `∑_{x,y} c x c y (1 − cos((x−y)s)) = −((∑ c x cos(x s))² + (∑ c x sin(x s))²) ≤ 0`, using `∑ c = 0`.
  Combining these (swapping the finite sum with the integral) yields `K · (∑∑ c x c y |x−y|^q) = ∫_(0,∞) (nonpositive) ≤ 0`, and dividing by `K > 0` gives the result.

- **q = 2 (`neg_type_two`)** is purely algebraic: `∑∑ c x c y (x−y)² = −2 (∑ c x · x)² ≤ 0` when `∑ c = 0`.
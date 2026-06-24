# Status: Four-point Ptolemaic snowflake theorem (`thm:q5-four-point-ptolemaic`)

This file records the state of the formalization of
**"Every four-point Ptolemaic metric has `q`-negative type for `0 < q ≤ log₂ 3`"**
(Theorem `thm:q5-four-point-ptolemaic` of `part2_sandwiches.tex`).

All work is in `RequestProject/Ptolemaic.lean` (which imports `RequestProject/Main.lean`
and `RequestProject/ExpKernel.lean`, and reuses the previously-proved line-metric
result `NegType.real_finite_negative_type`).

## Update

* **`blumenthal_negType` (the classical range `0 < q ≤ 1`) is now fully proved**
  (no `sorry`, axioms only `propext`, `Classical.choice`, `Quot.sound`).  This was
  done by building, from scratch, the conditionally-negative-type / Schoenberg
  kernel theory in the new self-contained file `RequestProject/ExpKernel.lean`:
  the Schur product theorem (`QPos.mul`), Schur powers (`QPos.pow`), the
  exponential kernel (`QPos.exp`), the Gaussian / negative-distance kernel
  (`qpos_exp_neg_dist`), the resolvent kernel (`qpos_resolvent`), and the
  downward-closure theorem (`qpos_downward`).  In `Ptolemaic.lean` this is
  combined with the new lemmas `metric4_det_q1_nonneg` (every four-point metric has
  nonnegative Schoenberg determinant at `q = 1`, proved via an explicit cut/
  Gromov-product decomposition certificate `det_gromov_nonneg`), `metric4_one_negType`
  (every four-point metric has `1`-negative type), and `metric4_qpos_gram`.
  `ExpKernel.lean` is entirely `sorry`-free.

* The **only remaining `sorry`** in the project is `schoenberg_det_nonneg` (see
  below).  Because `four_point_ptolemaic_negType` is assembled from it, the main
  theorem still depends on this single `sorry`.

## Statement (faithful, in `RequestProject/Ptolemaic.lean`)

```
theorem four_point_ptolemaic_negType {q : ℝ} (hq0 : 0 < q) (hq : q ≤ Real.logb 2 3)
    (d : Fin 4 → Fin 4 → ℝ) (hm : IsMetric4 d) (hp : IsPtolemaic4 d) :
    HasNegType q d
```

with `IsMetric4`, `IsPtolemaic4`, `HasNegType` the obvious four-point definitions.

## Fully proved (no `sorry`, axioms only `propext`, `Classical.choice`, `Quot.sound`)

The complete supporting framework of the paper's proof:

- **Schoenberg's criterion** (`lem:q5-schoenberg`), both directions, for the
  `3×3` matrix based at point `3`:
  `negType_of_schoenberg` (PSD ⇒ negative type) and
  `det_nonneg_of_negType` (negative type ⇒ determinant ≥ 0), plus the algebraic
  PSD fact `psd3_of_minors` and the one-entry concavity `schoenDet_ge_of_endpoints`
  (`lem:q5-one-entry-concavity`).
- **The star inequality** (`lem:q5-star`) in full: `star_inequality`, reduced
  through `star_uv`, `star_single`, and the genuine calculus core
  `star_single_p0` / `psi_key` / `theta_nonneg` / `xi_antitoneOn` / `logb32_bounds`
  / `three_rpow_logb`.
- **`2×2` minor nonnegativity** (snowflaked triangles are Euclidean): `minor_nonneg`.
- **Line metrics** (`lem:q5-line-metrics`): `line_negType` / `embed_real_negType`,
  transporting `NegType.real_finite_negative_type` to `Fin 4`.
- **Star metrics** (`lem:q5-star-metrics`): `star_negType`, with `star_det_nonneg`.
- **Relabelling invariance** of negative type: `hasNegType_reindex`.
- **Metric inversion as a diagonal congruence** of the Schoenberg matrix:
  `schoenDet_congr` (the algebraic content of `lem:q5-inversion-euclidean`).
- **The attached-ray extension** (`lem:q5-attached-ray`): `attached_ray_negType`,
  with its endpoint determinants `endpoint_star_det`, `endpoint_line_det`.
- **The metric-inversion / Ptolemy-equality endpoint** of the geodesic-insertion
  lemma (`lem:q5-radial`): `geodesic_ptolemy_endpoint_det` — the crux step,
  combining inversion (`schoenDet_congr`), the attached-ray lemma, and relabelling.

## Remaining (currently `sorry`)

- `schoenberg_det_nonneg`: the determinant case-analysis (the heart of the paper's
  proof).  All mechanisms it needs are proved above; what remains is the
  combinatorial assembly: fixing the leaf lengths and reducing each off-diagonal
  entry to the endpoints of its feasible interval by concavity
  (`schoenDet_ge_of_endpoints`), each endpoint being a geodesic-insertion
  configuration handled by `attached_ray_negType` / `line_negType` /
  `star_negType` / `geodesic_ptolemy_endpoint_det` (after relabelling), together
  with the polytope/feasibility bookkeeping.  This is the variational
  (negative-minimizer / active-constraint) argument of the paper and is the single
  remaining `sorry` in the project.

The main theorem `four_point_ptolemaic_negType` is assembled from this, so it
currently depends on the one `sorry` above and is **not yet fully proved**.

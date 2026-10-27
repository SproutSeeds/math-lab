# The PPT criterion in Lean

Date: 26 October 2026. Labels: Exact / Verified / Heuristic / Conjecture (ORP).

## Result (Verified)

- `ChainPPT.ppt_criterion`. For `d₁, d₂ ≥ 2`, `AllPPTSeparable d₁ d₂ ↔ d₁ * d₂ ≤ 6`: every PPT operator
  on `ℂ^{d₁} ⊗ ℂ^{d₂}` is separable exactly when `d₁ d₂ ≤ 6` (Peres 1996; Horodecki, Horodecki and
  Horodecki 1996; with Størmer's and Woronowicz's theorems).
- `ChainPPT.allPPTSeparable_iff_allDecomposable`. In every dimension, every PPT operator on `ℂⁿ ⊗ ℂᵐ` is
  separable exactly when every positive map `Mₙ → Mₘ` is decomposable.
- `ChainPPT.pptSeparable23`. Woronowicz's theorem in state form: every PPT operator on `ℂ² ⊗ ℂ³` is
  separable.
- `ChainPPT.isSeparable_iff_isPPT`. When `d₁ d₂ ≤ 6`, an operator is separable exactly when it is PPT.
  One direction, `isPPT_of_isSeparable` (Peres's criterion), holds in every dimension.
- `ChainPPT.exists_ppt_entangled`. When `d₁ d₂ > 6` there is a PPT operator that is not separable.
  `ChainPPT.rho33_ppt_entangled` gives an explicit one on `ℂ³ ⊗ ℂ³` with rational entries.
- `ChainPPT.isClosed_separable`. The separable cone is closed.
- `MathLab.isCompact_convexHull`. In a finite-dimensional real vector space, the convex hull of a compact
  set is compact. Mathlib has only the case of a finite set.

The definitions are those of `Duality.lean`, unchanged:

- `IsPPT ρ`: ρ and its partial transpose are positive semidefinite.
- `IsSeparable ρ`: ρ is a finite sum of product projectors `|x ⊗ y⟩⟨x ⊗ y|`.

Operators are not normalized. Scaling to trace one changes neither notion.

None of these statements is vacuous:

- `rho33_ppt_entangled` exhibits a PPT operator that is not separable.
- `pptSeparable23` makes every PPT operator on `ℂ² ⊗ ℂ³` separable.
- `isPPT_of_isSeparable` makes every separable operator PPT.

## Verification hook

```sh
cd math-lab
lake build MathLab        # Build completed successfully; every `#print axioms` line lists only
                          # propext, Classical.choice, Quot.sound
python3 scripts/check.py  # "pass": true, "standard_axioms_only": true; 0 sorry, 0 warnings in MathLab/
```

The toolchain (Lean v4.35.0-rc4) and Mathlib (`1b3c419`) are pinned.

**Verification record: PASS**, 26 Oct 2026. In `results/check.json`:

- 284 theorems;
- standard axioms only;
- no `sorry`;
- no warnings in `MathLab/`.

## The proof, file by file

| Step | Statement | Where |
|---|---|---|
| 1 | Carathéodory with `d + 1` points, so convex hulls of compact sets are compact in dimension `d` | `Convex/CompactHull.lean`: `exists_convexComb_fin`, `isCompact_convexHull` |
| 2 | Product states (product projectors of trace one) form a compact set: the image of pairs of unit vectors | `ChainTheory/PPTCriterion.lean`: `isCompact_prodStates` |
| 3 | Separable operators of trace at most one are the convex hull of 0 and the product states. So they form a compact set, and the separable cone is closed | `PPTCriterion.lean`: `sepBall_eq`, `isCompact_sepBall`, `isClosed_separable` |
| 4 | A Hermitian, block-positive `W` is the Choi matrix of a positive map | `PPTCriterion.lean`: `choiInv`, `choi_choiInv`, `isPositive_choiInv` |
| 5 | The Choi matrix of a decomposable map is `P + pt Q` with `P, Q ⪰ 0`, so it is nonnegative on PPT operators | `PPTCriterion.lean`: `choi_eq_of_kraus`, `pair_choi_nonneg_of_decomposable` |
| 6 | Hahn–Banach, explained below | `PPTCriterion.lean`: `allPPTSeparable_of_allDecomposable` |
| 7 | With the states-to-maps direction (`Duality.lean`), PPT = separable exactly when all positive maps are decomposable. The read cap (`Woronowicz.lean`) says when | `PPTCriterion.lean`: `allPPTSeparable_iff_allDecomposable`, `ppt_criterion` |

Step 6 runs as follows.

- Suppose a PPT operator lies outside the closed separable cone. Hahn–Banach gives a Hermitian `W` that is
  negative on that operator.
- `W` is nonnegative on the separable cone. That cone contains every product projector, so `W` is block
  positive.
- By step 4, `W` is the Choi matrix of a positive map. That map is decomposable by hypothesis, so by step 5
  `W` is nonnegative on every PPT operator. This contradicts the first point.

The criterion is assembled on the map side:

- The read cap (`ChainWoronowicz.readcap`) supplies Størmer's theorem, Woronowicz's theorem and the dark
  direction. The two dualities carry them to states.
- Swapping the two factors (`allPPTSeparable_symm`) also goes through maps, via the adjoint map
  (`ChainReadCap.allDecomposable_symm`).
- For `d₁ d₂ > 6` the entangled PPT operators come from Hahn–Banach, so they are not explicit in
  general. The positive maps behind them are explicit: the Choi map, and an integer map `M₂ → M₄`.

## Where it departs from the literature

- **Closedness.** The usual proof that the separable cone is closed cites Carathéodory and compactness
  without detail. Here Carathéodory is used with a fixed number of points, padded with zero weights. The
  set of separable operators of trace at most one is written as the convex hull of 0 and the product
  states. Adding 0 to the hull covers the dimensions in which there are no product states.
- **Inverse Choi.** `choiInv W` is defined by the formula `Φ(X)ₖₗ = Σ X_{ab} W_{(a,k),(b,l)}`, and its
  positivity is read off from `choi_prodVec`, which is already proved.

## Limits

- The dark witness for `ℂ² ⊗ ℂ⁴` (`ChoiDark.rho24`) is not restated in this vocabulary.
  `exists_ppt_entangled` covers that case without an explicit witness.
- Explicit witnesses in larger dimensions, for example `rho33` embedded by local isometries, are not
  stated.

## Credits

- A. Peres, Phys. Rev. Lett. 77 (1996) 1413.
- M., P. and R. Horodecki, Phys. Lett. A 223 (1996) 1.
- E. Størmer, Acta Math. 110 (1963) 233.
- S. L. Woronowicz, Rep. Math. Phys. 10 (1976) 165.
- The explicit state `rho33` is `σ_{7/2}` of the one-parameter family of P., M. and R. Horodecki, Phys. Rev.
  Lett. 82 (1999) 1056. It is PPT, and the Choi map's Choi matrix is negative on it (`ChoiDark.lean`).

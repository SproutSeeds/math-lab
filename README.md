# math-lab

Lean 4 proofs about positive maps and entanglement, on a pinned Mathlib. The library grew out of an audit
of the read cap in A. D. Wissner-Gross's Chain Theory
([github.com/SproutSeeds/chain-theory-audit](https://github.com/SproutSeeds/chain-theory-audit)).

## Main results

Every headline theorem uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and no
`sorry`. `MathLab/` has 343 theorems; `results/check.json` records the check.

| Theorem | Statement |
|---|---|
| `ChainPPT.ppt_criterion` | **The PPT criterion** (Peres; Horodecki, Horodecki and Horodecki 1996): for d₁, d₂ ≥ 2, every PPT state on ℂ^{d₁} ⊗ ℂ^{d₂} is separable exactly when d₁d₂ ≤ 6 |
| `ChainPPT.allPPTSeparable_iff_allDecomposable` | States and maps: every PPT state on ℂⁿ ⊗ ℂᵐ is separable exactly when every positive map Mₙ → Mₘ is decomposable |
| `ChainLowRank.sep_of_rank_le_rank_redB` | **PPT states of low rank** (Kraus, Cirac, Karnas and Lewenstein 2000): for every m, a PPT state on ℂ² ⊗ ℂᵐ whose rank is at most that of its reduced state on ℂᵐ is separable |
| `ChainLowRank.rho24M_sharp` | The rank condition is sharp: P. Horodecki's PPT entangled state on ℂ² ⊗ ℂ⁴ has rank 5, one more than its reduced state |
| `ChainReduction.sep_of_rank_le_two` | **Rank-two PPT states are separable** (P. Horodecki, Smolin, Terhal and Thapliyal 2003), in every dimension |
| `ChainReduction.reduction_criterion`, `ChainReduction.rank_redA_le` | The reduction criterion: a PPT state satisfies ρ ⪯ ρ_A ⊗ 1, and so has rank at least that of each reduced state |
| `ChainWoronowicz.woronowicz` | **Woronowicz's theorem** (1976): every positive linear map M₂(ℂ) → M₃(ℂ) is decomposable |
| `ChainStormer.stormer` | **Størmer's theorem** (1963): every positive linear map M₂(ℂ) → M₂(ℂ) is decomposable |
| `ChainWoronowicz.readcap` | The read cap (`ReadCap`, verbatim from the Letter's `ChainAlpha.lean`). For d₁, d₂ ≥ 2, every positive map between M_{d₁} and M_{d₂}, in either direction, is decomposable exactly when d₁d₂ ≤ 6 |
| `ChoiDark.readable_imp_le_six` | The dark direction: when d₁d₂ > 6 there is a positive map that is not decomposable (the Choi map, and an explicit integer map M₂ → M₄) |
| `ChainDuality.allDecomposable_of_pptPairing` | States to maps: if every PPT state is nonnegative on the Choi matrix of every positive map, every positive map is decomposable |
| `ChainPPT.rho33_ppt_entangled`, `ChainPPT.rho24M_ppt_entangled` | Explicit PPT entangled states on ℂ³ ⊗ ℂ³ and ℂ² ⊗ ℂ⁴ with rational entries |
| `ChainPPT.isClosed_separable` | The separable cone is closed |
| `MathLab.isCompact_convexHull` | In a finite-dimensional real vector space, the convex hull of a compact set is compact |
| `ChainWoronowicz.extreme_rank_bound` | On an extreme ray of the PPT cone of ℂⁿ⊗ℂᵐ, r² + s² ≤ (nm)² + 1 for the ranks of ρ and its partial transpose |
| `MathLab.normal_spectral` | Spectral theorem for normal matrices |
| `MathLab.normal_completion_three` | Normal completions of 3 × 3 matrices (Kaliuzhnyi-Verbovetskyi, Spitkovsky and Woerdeman 2009, Thm 2.4) |

The proof of Woronowicz's theorem is laid out step by step in
[notes/2026-10-26-woronowicz-proof.md](notes/2026-10-26-woronowicz-proof.md), the PPT criterion in
[notes/2026-10-26-ppt-criterion.md](notes/2026-10-26-ppt-criterion.md), the low-rank theorem in
[notes/2026-10-27-low-rank.md](notes/2026-10-27-low-rank.md), and rank-two states in
[notes/2026-10-27-rank-two.md](notes/2026-10-27-rank-two.md).

## Definitions

`ChoiDark.lean` defines the notions the theorems use.

- `IsPositive Φ`: every quadratic form of `Φ(B†B)` is real and nonnegative.
- `IsDecomposable Φ`: Kraus form `Φ(X) = Σ K X K† + Σ L Xᵀ L†`.
- `Readable d₁ d₂`: every positive ℂ-linear map between M_{d₁} and M_{d₂}, in either direction, is decomposable.

`Duality.lean` defines the notions for states, on operators that need not have trace one:

- `IsPPT ρ`: ρ and its partial transpose are positive semidefinite.
- `IsSeparable ρ`: a finite sum of product projectors `|x ⊗ y⟩⟨x ⊗ y|`.

These are the corrected definitions of 26 October 2026. An earlier published version let the dark
direction hold vacuously; the audit repository records the correction.

## Files

| Path | What |
|---|---|
| `MathLab/ChainTheory/ChoiDark.lean` | Definitions; the dark direction of the read cap |
| `MathLab/ChainTheory/ReadCap.lean` | The read cap is equivalent to Woronowicz's theorem for M₂ → M₃ |
| `MathLab/ChainTheory/Duality.lean` | From PPT states to positive maps (Hahn–Banach) |
| `MathLab/ChainTheory/Stormer.lean` | Størmer's theorem, from the two-qubit theorem |
| `MathLab/ChainTheory/WoronowiczBase.lean` | Block matrices, local operations, separability from a normal dilation |
| `MathLab/ChainTheory/PPTFace.lean` | The face bound on extreme rays of the PPT cone |
| `MathLab/ChainTheory/Woronowicz.lean` | Woronowicz's theorem and the read cap |
| `MathLab/ChainTheory/PPTCriterion.lean` | The closed separable cone, from maps to states, and the PPT criterion |
| `MathLab/ChainTheory/LowRank.lean` | PPT states of low rank on ℂ² ⊗ ℂᵐ are separable; the rank condition is sharp |
| `MathLab/ChainTheory/Reduction.lean` | The reduction criterion, the rank inequality, and rank-two PPT states in every dimension |
| `MathLab/ChainTheory/ChainRP.lean` | Reflection positivity of mirror-symmetric webs of maximally entangled pairs |
| `MathLab/Positivity/NormalSpectral.lean` | Spectral theorem for normal matrices |
| `MathLab/Positivity/NormalCompletion.lean` | Normal completions of 3 × 3 matrices |
| `MathLab/Convex/CompactHull.lean` | Compact convex hulls in finite dimensions, via Carathéodory |
| `ThirdParty/PSI/` | Physical Superintelligence's two-qubit PPT-separability proof, vendored unchanged |

## Build and check

```sh
lake exe cache get        # once: the prebuilt Mathlib for the pinned commit (about 7 GB)
lake build MathLab        # each headline theorem prints its axioms
python3 scripts/check.py  # writes results/check.json: theorems, axioms, sorry and warnings per file
```

The toolchain is `leanprover/lean4:v4.35.0-rc4` and Mathlib is pinned at
`1b3c41969602424bd2f04b3d4f731734e5b00cde`.

## Credits and licenses

- Apache License 2.0 (`LICENSE`), copyright 2026 Cody Mitchell. The Chain Theory files were first
  published, on Lean 4.26, in SproutSeeds/chain-theory-audit.
- `ThirdParty/PSI/` is Physical Superintelligence PBC's proof that two-qubit PPT operators are separable
  (`twoQubit_ppt_separable`), under Apache-2.0 and unchanged. See its `LICENSE`, `NOTICE` and
  `PROVENANCE.md`. It supplies the 2 × 2 case.
- The PPT criterion is A. Peres, Phys. Rev. Lett. 77 (1996), and M., P. and R. Horodecki, Phys. Lett. A
  223 (1996). The explicit 3 × 3 state is from P., M. and R. Horodecki, Phys. Rev. Lett. 82 (1999).
- The rank-two theorem is P. Horodecki, J. A. Smolin, B. M. Terhal and A. V. Thapliyal, Theor. Comput. Sci.
  292 (2003); the reduction criterion is M. and P. Horodecki, Phys. Rev. A 59 (1999), and N. J. Cerf,
  C. Adami and R. M. Gingrich, Phys. Rev. A 60 (1999).
- The low-rank theorem is B. Kraus, J. I. Cirac, S. Karnas and M. Lewenstein, Phys. Rev. A 61 (2000). The
  2 × 4 state is from P. Horodecki, Phys. Lett. A 232 (1997).
- The route to Woronowicz's theorem comes from D. S. Kaliuzhnyi-Verbovetskyi, I. M. Spitkovsky and
  H. J. Woerdeman, "Matrices with normal defect one", Oper. Matrices 3 (2009), and from H. J. Woerdeman,
  Linear Algebra Appl. 376 (2004).
- Chain Theory and its Letter are A. D. Wissner-Gross's. These proofs are mathematics about positive
  maps; they neither confirm nor refute the theory's physics.

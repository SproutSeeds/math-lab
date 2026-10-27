# Woronowicz's theorem in Lean

Date: 26 October 2026. Labels: Exact / Verified / Heuristic / Conjecture (ORP).

## Result (Verified)

- `ChainWoronowicz.woronowicz : AllDecomposable 2 3`. Every positive linear map M₂(ℂ) → M₃(ℂ) is
  decomposable (Woronowicz, Rep. Math. Phys. 10 (1976) 165).
- `ChainWoronowicz.readable_two_three : Readable 2 3`. The (2,3) type is readable.
- `ChainWoronowicz.readcap : ReadCap Readable`. The alpha Letter's read cap, with no hypothesis: a type
  `(d₁, d₂)` with `d₁, d₂ ≥ 2` is readable exactly when `d₁ d₂ ≤ 6`.

The statements are the ones fixed on 26 Oct: positivity asks for real, nonnegative quadratic forms of
ℂ-linear maps, and decomposable means Kraus form `Σ K X K† + Σ L Xᵀ L†`. They are not vacuous:
`ChoiDark.dark_of_three_le` gives positive maps that are not decomposable, and `ReadCap.readable_one_one`
shows `Readable` can hold.

As far as we found, no proof assistant had Woronowicz's theorem before. PSI's
`PPTSubtraction.lean` calls the ℂ² ⊗ ℂ³ case "the separate Woronowicz obligation".

## Verification hook

```sh
cd math-lab
lake build MathLab        # Build completed successfully; every `#print axioms` line lists only
                          # propext, Classical.choice, Quot.sound
python3 scripts/check.py  # "pass": true, "standard_axioms_only": true; 0 sorry, 0 warnings in MathLab/
```

The toolchain (Lean v4.35.0-rc4) and Mathlib (`1b3c419`) are pinned. The check reads the messages that
Lake replays, so a cached build gives the same receipt.

**Verification record: PASS**, 26 Oct 2026. `results/check.json`: 243 theorems, standard axioms only,
no `sorry`.

## The proof, file by file

| Step | Statement | Where |
|---|---|---|
| 1 | Spectral theorem for normal matrices (Mathlib has only the Hermitian case) | `Positivity/NormalSpectral.lean`: `normal_spectral` |
| 2 | 3×3 normal completion: if `B†B − BB† = xx† − yy† ≠ 0`, some `z` and unit `ν` give `ν(B−z)†x = (B−z)y` (KSW Thm 2.4, Cor 2.11) | `Positivity/NormalCompletion.lean`: `normal_completion_three`, `exists_normal_dilation` |
| 3 | A normal `N` with corner `B` and `C ⪰ (NN†)₁₁` makes `[[1,B],[B†,C]]` separable (Woerdeman 2004, easy direction) | `ChainTheory/WoronowiczBase.lean`: `sep_of_normal_dilation` |
| 4 | Local operations `(G⊗M)ρ(G⊗M)†`: positivity, partial transpose, separability, extreme rays | `WoronowiczBase.lean`: `pt_lop`, `isPPT_lop`, `isSeparable_lop`, `isExtremePPT_lop` |
| 5 | Face bound: on an extreme ray of the PPT cone, `r² + s² ≤ D² + 1`, i.e. 37 for ℂ²⊗ℂ³ | `ChainTheory/PPTFace.lean`: `extreme_rank_bound` |
| 6 | Base case `[[1,B],[B†,C]]` on an extreme ray: `C = B†B`, `C = BB†`, or both Schur complements rank one, then step 2 and step 3 | `ChainTheory/Woronowicz.lean`: `sep_of_extreme_normalized` |
| 7 | If `ρ₀₀ + ρ₁₁` is singular, ρ lives on ℂ²⊗ℂ² and PSI's two-qubit theorem applies | `Woronowicz.lean`: `sep_of_corner_kernel` |
| 8 | Otherwise a real shear `z ∈ {1,2,3,4}` makes the corner invertible (four `C`-orthogonal kernel vectors cannot fit in ℂ³); normalize to `[[1,B],[B†,C]]` | `Woronowicz.lean`: `exists_shear`, `sep_of_extreme` |
| 9 | Krein–Milman: trace-one PPT operators are the closed convex hull of their extreme points, so every PPT operator pairs nonnegatively with every Choi matrix of a positive map | `Woronowicz.lean`: `ppt_pairing_nonneg` |
| 10 | Hahn–Banach duality, pairing form, gives the map statement | `Duality.lean`: `allDecomposable_of_pptPairing`; `Woronowicz.lean`: `woronowicz`, `readcap` |

## Where it departs from the paper

The route is Kaliuzhnyi-Verbovetskyi, Spitkovsky and Woerdeman, Oper. Matrices 3 (2009), Thm 5.2. Three
pieces are done differently:

- **Extreme rays.** KSW cite Hildebrand's count and write each PPT state as a sum of extreme rays. We
  prove the count directly (a dimension argument on `{F† Y F}` and its partial transpose). We then use
  Mathlib's Krein–Milman with the closed half-spaces from the duality, so neither Carathéodory nor the
  closedness of the separable cone is needed.
- **The 3×3 completion.** The paper's Lemmas 2.7–2.10, specialized to n = 3, become explicit formulas
  for `ν` and `z` in an eigenbasis of `B†B − BB† = diag(d, −d, 0)`. The formulas were checked
  numerically before formalizing: worst residual 2·10⁻¹⁰ over 2,000 random cases.
- **Singular corners.** KSW cite Woerdeman's Prop 3.1. We use steps 7 and 8 instead.

## Limits

- The state form "every PPT state on ℂ²⊗ℂ³ is separable" is not stated yet. We have its dual: every PPT
  state is nonnegative on every block-positive Choi matrix. The exact state form needs the separable
  cone to be closed, which is the converse-duality item on the roadmap.
- The Lean 4.26 files in the chain-theory-audit repository do not have this proof; it lives here, on
  Lean 4.35.

## Credits

- Route: Kaliuzhnyi-Verbovetskyi, Spitkovsky and Woerdeman (2009); Woerdeman, Linear Algebra Appl.
  376 (2004).
- Two-qubit separability: Physical Superintelligence's `twoQubit_ppt_separable`, vendored unchanged
  under `ThirdParty/PSI` (Apache-2.0).

# math-lab

Our Lean 4 library on a pinned, fully built Mathlib. Private.

| Path | What |
|---|---|
| `MathLab/ChainTheory/ChainRP.lean` | Reflection positivity of mirror-symmetric webs of maximally entangled pairs |
| `MathLab/ChainTheory/ChoiDark.lean` | The dark direction of the read cap (Choi map; an integer map M₂ → M₄) |
| `MathLab/ChainTheory/ReadCap.lean` | The read cap is equivalent to Woronowicz's theorem for M₂ → M₃ |
| `MathLab/ChainTheory/Duality.lean` | If every PPT state on ℂⁿ⊗ℂᵐ is separable, every positive map Mₙ → Mₘ is decomposable |
| `MathLab/ChainTheory/Stormer.lean` | Størmer's theorem: every positive map M₂ → M₂ is decomposable; the (2,2) type is readable |
| `MathLab/ChainTheory/Woronowicz.lean` | **Woronowicz's theorem**: every positive map M₂ → M₃ is decomposable; the read cap with no hypothesis |
| `MathLab/ChainTheory/WoronowiczBase.lean`, `PPTFace.lean` | Block matrices, local operations, normal dilations, the face bound r² + s² ≤ 37 |
| `MathLab/Positivity/NormalSpectral.lean` | Spectral theorem for normal matrices |
| `MathLab/Positivity/NormalCompletion.lean` | Normal completions of 3 × 3 matrices (KSW 2009, Thm 2.4) |
| `ThirdParty/PSI/` | Physical Superintelligence's two-qubit PPT-separability proof, vendored unchanged (Apache-2.0) |

Proof note: [notes/2026-10-26-woronowicz-proof.md](notes/2026-10-26-woronowicz-proof.md).

## Build

```sh
lake exe cache get   # once: fetch the prebuilt Mathlib for the pinned commit
lake build           # builds MathLab and the vendored modules it uses
```

Toolchain `leanprover/lean4:v4.35.0-rc4`; Mathlib `1b3c41969602424bd2f04b3d4f731734e5b00cde`.

## Provenance and licenses

- Our files: Copyright 2026 Cody Mitchell. Ported from github.com/SproutSeeds/chain-theory-audit
  (Apache-2.0), where the Lean 4.26 versions remain published.
- `ThirdParty/PSI/`: Copyright 2026 Physical Superintelligence PBC, Apache License 2.0. See its
  `LICENSE`, `NOTICE` and `PROVENANCE.md`.

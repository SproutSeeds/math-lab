# PPT² on M₃ in Lean

Date: 28 October 2026. Labels: Exact / Verified / Heuristic / Conjecture (ORP).

## Result (Verified)

- `Channels.pptSquared_three`. **The composition of any two PPT maps on M₃ is entanglement breaking**
  (Christandl, Müller-Hermes and Wolf 2019; Chen, Yang and Tang 2019). This is the PPT² conjecture of
  M. Christandl, on M₃.
- `Channels.isSchmidtLE_two_of_isPPT`. Every PPT operator on ℂ³ ⊗ ℂ³ has Schmidt number at most 2. This is the
  dual form of Yang, Leung and Tang's 2016 theorem that every 2-positive map M₃ → M₃ is decomposable.
- `Channels.isSchmidtLE_two_of_topBlock`. The lifting lemma (Chen, Yang and Tang 2017, Lemma 15(i); Turturean
  and Bao 2026, Lemma 4). If the compression of a positive operator on ℂ³ ⊗ ℂⁿ to the first two reference
  coordinates is separable, the operator has Schmidt number at most 2.
- `Channels/Basic.lean`, the channel layer:
  - completely positive, PPT and entanglement breaking maps (`IsCP`, `IsPPTMap`, `IsEB`), defined by the Choi
    matrix;
  - their operational meaning for every ancilla (`isCP_iff`, `isPPT_applyR`, `isEB_iff`);
  - the conjecture as a statement, `PPTSquared d`, and its Choi-state form (`pptSquared_iff`);
  - `pptSquared_two`;
  - `exists_isPPTMap_not_isEB`: one PPT map on M₃ need not be entanglement breaking (the map whose Choi matrix
    is the tiles state).
- `Channels/Schmidt.lean`: Schmidt number (`IsSchmidtLE`), with `isSchmidtLE_one_iff` (Schmidt number one is
  separability), and the reduction below.

The definitions match the operational ones:

- `isCP_iff`: a map is completely positive exactly when `id ⊗ Φ` is positive for every ancilla ℂʳ.
- `isEB_iff`: a map is entanglement breaking exactly when `id ⊗ Φ` sends every positive operator, for every
  ancilla, to a separable one.

None of the statements is vacuous:

- `exists_isPPTMap_not_isEB` shows the composition matters.
- `not_schmidt_route_four` shows the same argument cannot work on M₄.

**Status of the conjecture.**

- **In general, false (claimed).** An unrefereed preprint of 27 September 2026 (OpenAI,
  github.com/openai/math) gives two PPT maps on M₁₀ whose composition is not entanglement breaking, with a
  Lean formalization.
- **M₄ to M₉: open**, as far as we found.
- **A general bound.** Turturean and Bao (2026, with a Lean formalization) show that any 2(d − 1) PPT maps on
  M_d compose to an entanglement breaking map.

## Verification hook

```sh
cd math-lab
lake build MathLab        # Build completed successfully; every `#print axioms` line lists only
                          # propext, Classical.choice, Quot.sound
python3 scripts/check.py  # "pass": true, "standard_axioms_only": true; 0 sorry, 0 warnings in MathLab/
```

**Verification record: PASS**, 28 Oct 2026. In `results/check.json`:

- 450 theorems;
- standard axioms only;
- no `sorry`;
- no warnings in `MathLab/`.

## The proof

| Step | Statement | Where |
|---|---|---|
| 1 | Choi-state form. `C(Φ ∘ Ψ) = (id ⊗ Φ)(C(Ψ))`, so PPT² on M_d says that a PPT map on the second factor sends every PPT operator on ℂᵈ ⊗ ℂᵈ to a separable one | `choi_comp`, `pptSquared_iff` |
| 2 | Composition. Details below | `isEB_comp_of_isSchmidtLE` |
| 3 | The lifting lemma. Details below | `isSchmidtLE_two_of_topBlock` |
| 4 | Qutrits. The top block of a PPT operator on ℂ³ ⊗ ℂ³ is PPT on ℂ² ⊗ ℂ³, hence separable by Woronowicz's theorem. By step 3 the operator has Schmidt number at most 2 | `isPPT_topBlock`, `isSchmidtLE_two_of_isPPT` |
| 5 | PPT² on M₃. Steps 2 and 4 with k = 2, and the 2 × 3 PPT criterion once more | `pptSquared_three_of_schmidt`, `pptSquared_three` |
| 6 | Why the route stops at M₄. No Schmidt bound k works on M₄. For k ≤ 1 there are PPT entangled states on ℂ⁴ ⊗ ℂ⁴. For k ≥ 2, PPT operators on ℂᵏ ⊗ ℂ⁴ need not be separable, since 4k > 6 | `not_schmidt_route_four` |

Step 2 runs as follows.

- Suppose the Choi matrix of Ψ has Schmidt number at most k, Φ is PPT, and PPT operators on ℂᵏ ⊗ ℂᵖ are
  separable.
- Each pure part of C(Ψ) is `(W ⊗ 1) u` for some W: ℂᵏ → ℂⁿ, so it lives on ℂᵏ ⊗ ℂᵐ.
- `id ⊗ Φ` commutes with W on the first factor and sends that part to a PPT operator on ℂᵏ ⊗ ℂᵖ, which is
  separable.
- So Φ ∘ Ψ is entanglement breaking.

Step 3 runs as follows.

- Write the operator with top block D, cross block K and bottom block T.
- Build the pseudo-inverse `D⁺ = W (Wᴴ D W)⁻¹ Wᴴ` from an isometry W onto the support of D.
- Positivity puts the cross block on that support, so `D D⁺ K = K`. The generalized Schur complement gives
  `T − Kᴴ D⁺ K ⪰ 0`.
- With `D = Σ_s f_s f_s†` for product vectors f_s:
  `ρ = Σ_s (f_s ⊕ Kᴴ D⁺ f_s)(f_s ⊕ Kᴴ D⁺ f_s)† + (0 ⊕ (T − Kᴴ D⁺ K))`.
- Each vector there is a sum of two product vectors.

## Choices made here

- **The Schmidt-number bound.** It comes from Woronowicz's theorem and the lifting lemma, not from Yang, Leung
  and Tang's theorem on 2-positive maps. So the whole proof rests on Woronowicz's theorem (`Woronowicz.lean`)
  and elementary matrix analysis.
- **The pseudo-inverse.** It is built from the support isometry of `exists_support` (`Reduction.lean`). That
  lemma now holds for matrices indexed by any finite type.
- **Definitions.** Entanglement breaking is defined by the Choi matrix, and `isEB_iff` proves it equivalent to
  the definition for every ancilla. The same holds for complete positivity (`isCP_iff`), with a Kraus form from
  the spectral theorem.

## Limits

- **Dimension three only.** On M₄ the question is open as far as we found.
- **Maps, not only channels.** `PPTSquared d` concerns two PPT maps, which need not be trace preserving or
  equal. That covers squares of a single map and compositions of channels.

## Credits

- M. Christandl, A. Müller-Hermes and M. M. Wolf, "When do composed maps become entanglement breaking?",
  Ann. Henri Poincaré 20 (2019) 2295, arXiv 1807.01266.
- L. Chen, Y. Yang and W.-S. Tang, Phys. Rev. A 99 (2019) 012337, arXiv 1807.03636. Their earlier paper,
  Quantum Inf. Process. 16 (2017) 75, gives the lifting lemma.
- Y. Yang, D. H. Leung and W.-S. Tang, Linear Algebra Appl. 503 (2016) 233.
- D. Turturean and N. Bao, "Entanglement Breaking after 2(d−1) PPT Maps" (Physical Superintelligence, 2026).
- The two-qubit separability theorem used for `pptSquared_two` is Physical Superintelligence's
  `twoQubit_ppt_separable`, vendored unchanged under `ThirdParty/PSI` (Apache-2.0).

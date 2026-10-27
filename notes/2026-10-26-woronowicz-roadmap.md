# Roadmap: a formal proof of the read cap

Date: 26 October 2026. Labels: Exact / Verified / Heuristic / Conjecture (ORP).

## Where we are

| Step | Statement | Status |
|---|---|---|
| Dark direction | every type with d₁d₂ ≥ 8 has a positive non-decomposable map | Verified (`ChoiDark.readable_imp_le_six`) |
| Reduction | `ReadCap Readable ↔ Woronowicz23` (maps M₂ → M₃) | Verified (`ReadCap.readcap_iff_woronowicz`) |
| States to maps | PPT = separable on ℂⁿ⊗ℂᵐ ⇒ all positive maps Mₙ → Mₘ decomposable | Verified (`Duality.allDecomposable_of_allPPTSeparable`) |
| Størmer | every positive map M₂ → M₂ is decomposable; the (2,2) type is readable | Verified (`Stormer.stormer`, `Stormer.readable_two_two`; uses PSI's `twoQubit_ppt_separable`) |
| Woronowicz | every positive map M₂ → M₃ is decomposable | Verified (`Woronowicz.woronowicz`; see the proof note) |
| Read cap | `ReadCap Readable` with no hypothesis | Verified (`Woronowicz.readcap`) |
| Maps to states | all positive maps Mₙ → Mₘ decomposable ⇒ PPT = separable on ℂⁿ⊗ℂᵐ | Verified (`PPTCriterion.allPPTSeparable_of_allDecomposable`) |
| PPT criterion | for d₁, d₂ ≥ 2, PPT = separable on ℂ^{d₁}⊗ℂ^{d₂} exactly when d₁d₂ ≤ 6 | Verified (`PPTCriterion.ppt_criterion`; see the PPT criterion note) |
| Low rank | PPT on ℂ²⊗ℂᵐ with rank ρ ≤ rank ρ_B ⇒ separable, for every m; sharp | Verified (`LowRank.sep_of_rank_le_rank_redB`, `LowRank.rho24M_sharp`; 27 Oct 2026) |
| Rank two | PPT on ℂⁿ⊗ℂᵐ with rank ρ ≤ 2 ⇒ separable, every n, m; the reduction criterion | Verified (`Reduction.sep_of_rank_le_two`, `Reduction.reduction_criterion`; 27 Oct 2026) |
| Rank four | a PPT entangled state of rank 4 (tiles UPB); the range criterion | Verified (`Tiles.tiles_ppt_entangled`; 27 Oct 2026) |
| Rank three | PPT with rank ρ ≤ 3 ⇒ separable, via the M × N low-rank theorem (Horodecki, Lewenstein, Vidal and Cirac 2000) | Verified (`LowRankMN.sep_of_rank_le_three`, `LowRankMN.sep_of_rank_le_max`; 27 Oct 2026) |
| Minimal rank | the minimal rank of PPT entanglement is four | Verified (`LowRankMN.min_rank_ppt_entangled`; see the minimal-rank note) |

## The remaining theorem: PPT ⇒ separable on ℂ²⊗ℂ³

**Done on 26 Oct 2026**, in dual form; see [the proof note](2026-10-26-woronowicz-proof.md). The plan below
was followed with changes: Krein–Milman replaced the extreme-ray decomposition, and the singular case was
handled by a two-qubit reduction and a shear.

Route chosen: Kaliuzhnyi-Verbovetskyi, Spitkovsky and Woerdeman, "Matrices with normal defect one",
Oper. Matrices 3 (2009), Thm 5.2 (https://files.ele-math.com/articles/oam-03-24.pdf). Sketch, to be
checked against the paper before formalizing:

1. **Reduce to extreme rays.** The PPT cone on ℂ²⊗ℂ³ is a closed convex cone. It is enough to show its
   extreme rays are separable, since every element is a finite sum of extreme rays (Krein–Milman /
   Carathéodory for cones; Mathlib has `KreinMilman` and `Caratheodory`).
2. **Face dimension.** For ρ on an extreme ray, Hildebrand's count gives rank(ρ)² + rank(ρ^Γ)² ≤ 37 in
   2×3. So either one of the ranks is at most 3, or both are 4.
3. **Low rank.** Write ρ as a 2×2 block matrix [[A, B], [B†, C]] with 3×3 blocks. In the low-rank case the
   PPT conditions force B to be normal (relative to A and C), and then ρ is separable (the KSW
   normal-matrix criterion).
4. **The (4,4) case.** Four vectors in ℂ³ are linearly dependent; this gives a "normal completion", and
   Woerdeman's 2004 theorem turns that into separability. The 2004 paper still has to be read.

Effort: weeks, not days. Step 3 is mostly linear algebra; step 4 depends on the 2004 paper.

Alternatives, if the route stalls:

- **Kraus–Cirac–Karnas–Lewenstein (2000).** Subtract product vectors from the range until the ranks
  are small. PSI's `PPTSubtraction.lean` formalizes this step conditionally, and says the existence of
  the directions in 2×3 "is still the separate Woronowicz obligation".
- **Aubrun–Szarek (2015), Remark 5.** A Brouwer fixed-point route. Brouwer's fixed-point theorem is not
  in Mathlib.

## Supporting work

- **The converse duality** (all positive maps decomposable ⇒ PPT = separable). **Done on 26 Oct 2026**
  (`PPTCriterion.lean`, with `Convex/CompactHull.lean` for the closed separable cone); see
  [the PPT criterion note](2026-10-26-ppt-criterion.md).
- **Refactor.** Move the general positivity results from `MathLab/ChainTheory/` to `MathLab/Positivity/`
  once the Woronowicz work starts importing them.

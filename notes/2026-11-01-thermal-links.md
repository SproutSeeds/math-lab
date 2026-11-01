# Why Chain Theory has no dynamics, and the smallest fix (1 Nov 2026)

File: `MathLab/ChainTheory/ThermalLinks.lean`. Every result uses only the standard axioms.

A link of qudit dimension n is a pair state ∑ X k l • e_k ⊗ e_l, written by its coefficient matrix X.
Chain Theory's link is the maximally entangled pair, X = 1 (unnormalized).

1. **Chains** (`join_pairOf`, `chain_eq_pow`): joining two links multiplies their coefficient matrices. A join
   projects the right end of one link and the left end of the next onto the pair ket. A chain of links is one
   link, and an operator inserted at a join enters the product (`join_insert`).
2. **Chain Theory's links are flat** (`eq_smul_one_of_matching_invariant`): a link left unchanged by every
   re-matching U ⊗ Ū, the axiom's "known" clause, is a multiple of the identity.
3. **Thermal links** (`thermal`): K_β = diag(e^{−βE_i/2}), the thermofield double of the energies E at inverse
   temperature β.
   - They are reflection positive (`isGram_thermal`, `thermal_rp`).
   - A chain of m + 1 of them is the thermal link at (m + 1)β (`chain_thermal`).
   - At β = 0 they are Chain Theory's link (`thermal_zero`).
4. **The transfer operator** T(B) = K B K governs correlations along a chain: across m links the correlation of
   A and B is tr(A Tᵐ(Bᵀ)) (`corr_pow`). For a thermal link, T multiplies the matrix unit e_i e_jᵀ by
   e^{−β(E_i+E_j)/2} (`transfer_thermal_single`). Correlations decay at rates set by the energies, which is a
   genuine Euclidean dynamics with Hamiltonian E.
5. **The no-go and its converse.**
   - The transfer operator of Chain Theory's link is a multiple of the identity
     (`transfer_of_matching_invariant`). Every correlation decays at one rate, and the reconstructed
     Hamiltonian has a single level.
   - A link that is both reflection positive and maximally entangled is a multiple of the identity
     (`eq_smul_one_of_isGram_of_maxEntangled`).
   - For thermal links at β > 0, three conditions coincide (`thermal_flat_iff`, `thermal_maxEntangled_iff`):
     maximal entanglement, a scalar transfer operator, and equal energies. A two-level example has genuine
     dynamics (`two_level_not_flat`).

**Reading.** Chain Theory's axiom ("nothing exists but maximally entangled pairs") is the infinite-temperature
point of an ordinary reflection-positive Euclidean chain. That is why its energy is a single constant
(compendium Part III: "a phase alone"). Any dynamics needs links that are not maximally entangled, which means
leaving the axiom as written.

The mathematics is standard: thermofield doubles, entanglement swapping, and the transfer matrix of a Euclidean
chain. What is checked here is the formal statement and its reading in Chain Theory's vocabulary. It neither
confirms nor refutes Chain Theory's physics beyond this structural point.

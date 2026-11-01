# The symmetry group of one link (1 Nov 2026)

Files: `MathLab/ChainTheory/LocalUnitary.lean`, `MathLab/ChainTheory/GaugeGroup.lean`. Every result below
uses only the standard axioms.

A link of type (f, c) is a maximally entangled pair of a qudit of dimension f and one of dimension c. Its
local basis changes are the unitaries A ⊗ B on ℂᶠ ⊗ ℂᶜ, the local-unitary group LU(f, c).

1. **When a Kronecker product is the identity** (`kronecker_eq_one_iff`): A ⊗ B = 1 exactly when A = a • 1
   and B = a⁻¹ • 1.
2. **Faithfulness** (`sHom_injective_iff`): the special product S(U(f) × U(c)), the pairs with
   det A · det B = 1, maps to LU(f, c) by (A, B) ↦ A ⊗ B. Its kernel is the pairs (λ • 1, λ⁻¹ • 1) with
   λ^{f−c} = 1, so the map is injective exactly when f and c differ by one. In that case it is onto
   (`sHom_range`), and `luEquiv : S(U(f) × U(c)) ≃* LU(f, c)`.
3. **The global form** (`gaugeEquiv`): (g, h, z) ↦ (z³ h, z̄² g) maps SU(3) × SU(2) × U(1) onto S(U(2) × U(3))
   (`smHom_surjective`). Its kernel is {(z² • 1, z̄³ • 1, z) : z⁶ = 1} (`ker_smHom`), which has six
   elements and is cyclic (`card_ker`, `isCyclic_ker`). So the local-unitary group of the qubit–qutrit
   link is (SU(3) × SU(2) × U(1)) ⧸ ℤ₆, the Standard Model gauge group in its global form.
4. **The selection** (`selection`, `readable_faithful_iff`): with the read cap proved
   (`ChainWoronowicz.readcap`), a readable type (d₁d₂ ≤ 6) with an acting central charge (d₁ ≠ d₂) is
   (2, 3) or (3, 2). These are also exactly the readable types on which the special product acts
   faithfully. This is the alpha Letter's `selection_under_read_cap` with its one hypothesis discharged.

The mathematics is classical (Baez and Huerta 2010 for item 3); what is new is the machine check and the
combination with the read cap. These are statements about positive maps and unitary groups. They neither
confirm nor refute Chain Theory's physical identifications.

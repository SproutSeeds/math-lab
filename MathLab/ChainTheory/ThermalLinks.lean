module

/-
ThermalLinks.lean

Why Chain Theory has no dynamics, and the smallest change that gives it some.

A link of qudit dimension n is written by its coefficient matrix X: the pair state ∑ X k l • e_k ⊗ e_l
(`ChainRP.vec X`). Chain Theory's link is the maximally entangled pair, X = 1 (unnormalized).

  Part 1  Chains. Joining two links (projecting the right end of the first and the left end of the second
          onto the pair ket ∑ₖ e_k ⊗ e_k) multiplies their coefficient matrices (`join_pairOf`); an
          operator inserted at a join enters the product (`insert_vec`). A chain of n links K is the link Kⁿ.
  Part 2  Chain Theory's links. A link left unchanged by every re-matching U ⊗ Ū (the "known" clause of the
          axiom) is a multiple of the identity (`eq_smul_one_of_matching_invariant`).
  Part 3  Thermal links. K_β = diag(e^{−βE_i/2}), the thermofield double of energies E at inverse temperature
          β. It is reflection positive (`isGram_thermal`, so `ChainRP.IsGram.rp` applies), a chain of m of
          them is the thermal link at mβ (`thermal_pow`), and β = 0 gives Chain Theory's link (`thermal_zero`).
  Part 4  The transfer operator B ↦ K B K, which carries correlations one link along a chain
          (`transfer_iterate`). For a thermal link it multiplies the matrix unit e_i e_jᵀ by
          e^{−β(E_i+E_j)/2} (`transfer_thermal_single`): a real spectrum, with the energy gaps of E.
  Part 5  The no-go. The transfer operator of Chain Theory's link is a multiple of the identity, so the
          reconstructed Hamiltonian has one level (`transfer_of_matching_invariant`). A link that is both
          reflection positive and maximally entangled is a multiple of the identity
          (`eq_smul_one_of_isGram_of_maxEntangled`). For thermal links, maximal entanglement, a scalar
          transfer operator and equal energies are the same condition (`thermal_flat_iff`,
          `thermal_maxEntangled_iff`). So dynamics needs links that are not maximally entangled.

The mathematics is standard (thermofield doubles, entanglement swapping, the transfer matrix of a Euclidean
chain); what is checked is the formal statement and its reading in Chain Theory's vocabulary.
-/
public import MathLab.ChainTheory.ChainRP
public import MathLab.ChainTheory.LocalUnitary
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Matrix.PEquiv

@[expose] public section

open Matrix
open scoped Kronecker

noncomputable section

namespace ChainThermal

open ChainRP

variable {n : Type} [Fintype n] [DecidableEq n]

/-! ## Part 1. Chains of links -/

/-- Two links side by side: `X` on qudits (1, 2) and `Y` on qudits (3, 4). -/
def pairOf (X Y : Matrix n n ℂ) : (n × n) × (n × n) → ℂ := fun p => ChainRP.vec X p.1 * ChainRP.vec Y p.2

/-- The join of qudits 2 and 3: projection onto the (unnormalized) pair ket ∑ₖ e_k ⊗ e_k, leaving 1 and 4. -/
def join (Ψ : (n × n) × (n × n) → ℂ) : n × n → ℂ := fun q => ∑ k, Ψ ((q.1, k), (k, q.2))

omit [DecidableEq n] in
/-- **Joining two links multiplies their coefficient matrices.** -/
theorem join_pairOf (X Y : Matrix n n ℂ) : join (pairOf X Y) = ChainRP.vec (X * Y) := by
  funext q
  simp [join, pairOf, ChainRP.vec, Matrix.mul_apply]

/-- An operator `O` on the left end of a link acts on its coefficient matrix by left multiplication. -/
theorem insert_vec (O Y : Matrix n n ℂ) : (O ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ ChainRP.vec Y = ChainRP.vec (O * Y) := by
  funext q
  simp only [mulVec, dotProduct, kroneckerMap_apply, one_apply, ChainRP.vec, mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Finset.sum_ite_eq, mul_comm]

omit [DecidableEq n] in
/-- A join with `O` inserted at the left end of the second link gives the link `X O Y`. -/
theorem join_insert (X O Y : Matrix n n ℂ) :
    join (pairOf X (O * Y)) = ChainRP.vec (X * O * Y) := by
  rw [join_pairOf, Matrix.mul_assoc]

/-- A chain of `m + 1` links `K`, joined one after another. -/
def chain (K : Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => K
  | m + 1 => chain K m * K

/-- **A chain of links is one link**: m + 1 links K joined in a row are the link K^{m+1}. -/
theorem chain_eq_pow (K : Matrix n n ℂ) (m : ℕ) : chain K m = K ^ (m + 1) := by
  induction m with
  | zero => simp [chain]
  | succ m ih => rw [chain, ih, ← pow_succ]

omit [DecidableEq n] in
theorem join_chain (K : Matrix n n ℂ) (m : ℕ) : join (pairOf (chain K m) K) = ChainRP.vec (chain K (m + 1)) := by
  rw [join_pairOf]; rfl

/-! ## Part 2. Chain Theory's links: invariance under every re-matching -/

/-- The diagonal unitary that flips the sign of `e_i`. -/
def signFlip (i : n) : Matrix n n ℂ := diagonal fun k => if k = i then -1 else 1

theorem signFlip_mem (i : n) : signFlip i ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff, signFlip, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

/-- The permutation unitary of the transposition of `i` and `j`. -/
def swapU (i j : n) : Matrix n n ℂ := (Equiv.swap i j).toPEquiv.toMatrix

theorem swapU_mul_self (i j : n) : swapU i j * swapU i j = 1 := by
  rw [swapU, PEquiv.toMatrix_toPEquiv_mul]
  ext a b
  simp [PEquiv.toMatrix_apply, one_apply, Equiv.swap_apply_self]

omit [Fintype n] in
theorem star_swapU (i j : n) : star (swapU i j) = swapU i j := by
  ext a b
  have e : ((Equiv.swap i j) b = a) = ((Equiv.swap i j) a = b) :=
    propext ⟨fun h => by rw [← h, Equiv.swap_apply_self], fun h => by rw [← h, Equiv.swap_apply_self]⟩
  simp only [swapU, star_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, e]
  split_ifs <;> simp

theorem swapU_mem (i j : n) : swapU i j ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff, star_swapU, swapU_mul_self]

theorem swapU_conj (i j : n) (X : Matrix n n ℂ) :
    swapU i j * X * star (swapU i j) = X.submatrix (Equiv.swap i j) (Equiv.swap i j) := by
  rw [star_swapU, swapU, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_swap]
  rfl

/-- **A link unchanged by every re-matching is a multiple of the identity.** The "known" clause of the axiom
asks a pair state to be invariant under every matching U ⊗ Ū, which acts on the coefficient matrix as
X ↦ U X Uᴴ (`ChainRP.mirrorMap_vec`); so Chain Theory's links are X = c • 1. -/
theorem eq_smul_one_of_matching_invariant (X : Matrix n n ℂ)
    (h : ∀ U ∈ unitaryGroup n ℂ, U * X * star U = X) (i₀ : n) : X = X i₀ i₀ • 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    have hs := congrFun (congrFun (h (swapU i i₀) (swapU_mem i i₀)) i) i
    rw [swapU_conj, submatrix_apply, Equiv.swap_apply_left] at hs
    rw [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
    exact hs.symm
  · have hs := congrFun (congrFun (h (signFlip i) (signFlip_mem i)) i) j
    rw [signFlip, star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal, diagonal_mul] at hs
    simp only [Pi.star_apply, Ne.symm hij, ite_true, ite_false, star_one] at hs
    rw [Matrix.smul_apply, one_apply_ne hij, smul_zero]
    linear_combination -hs / 2

/-! ## Part 3. Thermal links -/

/-- **The thermal link** K_β = diag(e^{−βE_i/2}): the thermofield double of the energies `E` at inverse
temperature `β`, unnormalized. -/
def thermal (β : ℝ) (E : n → ℝ) : Matrix n n ℂ := diagonal fun i => ((Real.exp (-(β * E i) / 2) : ℝ) : ℂ)

omit [Fintype n] in
/-- **At β = 0 the thermal link is Chain Theory's maximally entangled pair.** -/
theorem thermal_zero (E : n → ℝ) : thermal 0 E = 1 := by
  simp [thermal]

theorem thermal_mul (β γ : ℝ) (E : n → ℝ) : thermal β E * thermal γ E = thermal (β + γ) E := by
  rw [thermal, thermal, thermal, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

omit [Fintype n] in
theorem thermal_conjTranspose (β : ℝ) (E : n → ℝ) : (thermal β E)ᴴ = thermal β E := by
  rw [thermal, diagonal_conjTranspose]
  congr 1
  funext i
  rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

theorem thermal_pow (β : ℝ) (E : n → ℝ) (m : ℕ) : thermal β E ^ m = thermal (m * β) E := by
  induction m with
  | zero => simp [thermal_zero]
  | succ m ih =>
    rw [pow_succ, ih, thermal_mul]
    congr 1
    push_cast
    ring

/-- **A chain of thermal links is a thermal link**: m + 1 links at β are one link at (m + 1)β. -/
theorem chain_thermal (β : ℝ) (E : n → ℝ) (m : ℕ) : chain (thermal β E) m = thermal ((m + 1) * β) E := by
  rw [chain_eq_pow, thermal_pow]
  push_cast
  rfl

/-- **Thermal links are reflection positive**: their coefficient matrix has Gram form, so the
Osterwalder–Schrader form is real and nonnegative at every observable (`thermal_rp`). -/
theorem isGram_thermal (β : ℝ) (E : n → ℝ) : IsGram (thermal β E) :=
  ⟨n, inferInstance, thermal (β / 2) E, by rw [thermal_conjTranspose, thermal_mul, add_halves]⟩

theorem thermal_rp (β : ℝ) (E : n → ℝ) (F : Matrix n n ℂ) :
    0 ≤ (rpForm (thermal β E) F).re ∧ (rpForm (thermal β E) F).im = 0 :=
  (isGram_thermal β E).rp F

/-! ## Part 4. The transfer operator -/

/-- **The transfer operator** of a link `K`: it carries a correlation one link further along a chain. -/
def transfer (K B : Matrix n n ℂ) : Matrix n n ℂ := K * B * K

theorem transfer_iterate (K B : Matrix n n ℂ) (m : ℕ) : (transfer K)^[m] B = K ^ m * B * K ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, transfer]
    calc K * (K ^ m * B * K ^ m) * K = (K * K ^ m) * B * (K ^ m * K) := by simp only [Matrix.mul_assoc]
      _ = K ^ (m + 1) * B * K ^ (m + 1) := by rw [← pow_succ', ← pow_succ]

/-- The correlation of `A` at one end of a link `C` and `B` at the other. -/
def corr (C A B : Matrix n n ℂ) : ℂ := star (ChainRP.vec C) ⬝ᵥ ((A ⊗ₖ B) *ᵥ ChainRP.vec C)

omit [DecidableEq n] in
/-- `A ⊗ B` acts on a link as `C ↦ A C Bᵀ`. -/
theorem kron_mulVec_vec (A B C : Matrix n n ℂ) :
    (A ⊗ₖ B) *ᵥ ChainRP.vec C = ChainRP.vec (A * C * Bᵀ) := by
  funext q
  simp only [mulVec, dotProduct, kroneckerMap_apply, ChainRP.vec, Fintype.sum_prod_type, mul_apply,
    transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

omit [DecidableEq n] in
/-- The overlap of two links is the Hilbert–Schmidt inner product of their coefficient matrices. -/
theorem star_vec_dotProduct (C M : Matrix n n ℂ) : star (ChainRP.vec C) ⬝ᵥ ChainRP.vec M = trace (Cᴴ * M) := by
  simp only [dotProduct, ChainRP.vec, Pi.star_apply, Fintype.sum_prod_type, trace, diag, mul_apply,
    conjTranspose_apply]
  rw [Finset.sum_comm]

omit [DecidableEq n] in
theorem corr_eq_trace (C A B : Matrix n n ℂ) : corr C A B = trace (Cᴴ * A * C * Bᵀ) := by
  rw [corr, kron_mulVec_vec, star_vec_dotProduct]
  simp only [Matrix.mul_assoc]

/-- **The transfer operator governs correlations along a chain**: for a self-adjoint link `K`, the
correlation across m links is `tr (A Tᵐ(Bᵀ))` with `T = transfer K`. -/
theorem corr_pow (K A B : Matrix n n ℂ) (hK : Kᴴ = K) (m : ℕ) :
    corr (K ^ m) A B = trace (A * (transfer K)^[m] Bᵀ) := by
  rw [corr_eq_trace, conjTranspose_pow, hK, transfer_iterate]
  rw [show K ^ m * A * K ^ m * Bᵀ = K ^ m * (A * K ^ m * Bᵀ) by simp only [Matrix.mul_assoc], trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **The spectrum of a thermal transfer operator**: it multiplies the matrix unit `e_i e_jᵀ` by
e^{−β(E_i + E_j)/2}. Correlations decay at rates set by the energies. -/
theorem transfer_thermal_single (β : ℝ) (E : n → ℝ) (i j : n) :
    transfer (thermal β E) (single i j 1) = ((Real.exp (-(β * (E i + E j)) / 2) : ℝ) : ℂ) • single i j 1 := by
  ext a b
  simp only [transfer, thermal, diagonal_mul, mul_diagonal, Matrix.smul_apply, single_apply, smul_eq_mul]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ite_true, mul_one]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · simp [h]

/-! ## Part 5. The no-go, and its converse for thermal links -/

theorem transfer_smul_one (c : ℂ) (B : Matrix n n ℂ) : transfer (c • 1) B = (c * c) • B := by
  rw [transfer, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]

/-- **The no-go.** The transfer operator of a link invariant under every re-matching, Chain Theory's link, is a
multiple of the identity: every correlation decays at one rate, and the reconstructed Hamiltonian has a single
level. -/
theorem transfer_of_matching_invariant (X : Matrix n n ℂ) (h : ∀ U ∈ unitaryGroup n ℂ, U * X * star U = X)
    (i₀ : n) (B : Matrix n n ℂ) : transfer X B = (X i₀ i₀ * X i₀ i₀) • B := by
  have hX := eq_smul_one_of_matching_invariant X h i₀
  set c := X i₀ i₀
  rw [hX, transfer_smul_one]

/-- A link is maximally entangled when its reduced state `X Xᴴ` is a positive multiple of the identity. -/
def IsMaxEntangled (X : Matrix n n ℂ) : Prop := ∃ c : ℝ, 0 < c ∧ X * Xᴴ = (c : ℂ) • 1

open ComplexOrder in
/-- **A reflection-positive, maximally entangled link is a multiple of the identity**, so its transfer
operator is a multiple of the identity too (`transfer_smul_one`). -/
theorem eq_smul_one_of_isGram_of_maxEntangled {X : Matrix n n ℂ} (hG : IsGram X) (hM : IsMaxEntangled X) :
    ∃ s : ℝ, 0 < s ∧ X = (s : ℂ) • 1 := by
  obtain ⟨m, _, B, hB⟩ := hG
  obtain ⟨c, hc, hX⟩ := hM
  have hH : Xᴴ = X := by rw [hB, conjTranspose_mul, conjTranspose_conjTranspose]
  have hPSD : X.PosSemidef := hB ▸ posSemidef_conjTranspose_mul_self B
  set s := Real.sqrt c with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hc
  have hss : (s : ℂ) * (s : ℂ) = (c : ℂ) := by rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  refine ⟨s, hs, ?_⟩
  have hsq : (X - (s : ℂ) • 1) * (X + (s : ℂ) • 1) = 0 := by
    rw [hH] at hX
    simp only [sub_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul,
      hX, hss]
    abel
  have hPD : (X + (s : ℂ) • 1).PosDef :=
    Matrix.PosDef.posSemidef_add hPSD (Matrix.PosDef.one.smul (Complex.zero_lt_real.2 hs))
  exact sub_eq_zero.1 ((hPD.isUnit.mul_left_eq_zero).1 hsq)

/-- **For thermal links, dynamics and maximal entanglement exclude each other.** At β > 0 the transfer
operator is a multiple of the identity exactly when all the energies are equal. -/
theorem thermal_flat_iff {β : ℝ} (hβ : 0 < β) (E : n → ℝ) :
    (∃ c : ℂ, ∀ B, transfer (thermal β E) B = c • B) ↔ ∀ i j, E i = E j := by
  constructor
  · rintro ⟨c, hc⟩ i j
    have key : ∀ k, ((Real.exp (-(β * (E k + E k)) / 2) : ℝ) : ℂ) = c := fun k => by
      have := congrFun (congrFun (hc (single k k 1)) k) k
      rw [transfer_thermal_single, Matrix.smul_apply, Matrix.smul_apply, single_apply_same, smul_eq_mul,
        smul_eq_mul, mul_one, mul_one] at this
      exact this
    have h2 := (key i).trans (key j).symm
    have h3 : Real.exp (-(β * (E i + E i)) / 2) = Real.exp (-(β * (E j + E j)) / 2) := by exact_mod_cast h2
    have h4 := Real.exp_injective h3
    have : β * E i = β * E j := by linarith
    exact mul_left_cancel₀ hβ.ne' this
  · intro hE
    rcases isEmpty_or_nonempty n with h | h
    · exact ⟨0, fun B => Subsingleton.elim _ _⟩
    obtain ⟨i₀⟩ := h
    refine ⟨((Real.exp (-(β * E i₀) / 2) : ℝ) : ℂ) * ((Real.exp (-(β * E i₀) / 2) : ℝ) : ℂ), fun B => ?_⟩
    have hK : thermal β E = ((Real.exp (-(β * E i₀) / 2) : ℝ) : ℂ) • 1 := by
      rw [thermal, ← diagonal_one, ← diagonal_smul]
      congr 1
      funext i
      simp [hE i i₀]
    rw [hK, transfer_smul_one]

/-- **For thermal links at β > 0, maximal entanglement is the same condition: equal energies.** -/
theorem thermal_maxEntangled_iff {β : ℝ} (hβ : 0 < β) (E : n → ℝ) [Nonempty n] :
    IsMaxEntangled (thermal β E) ↔ ∀ i j, E i = E j := by
  have hsq : thermal β E * (thermal β E)ᴴ = thermal (β + β) E := by rw [thermal_conjTranspose, thermal_mul]
  constructor
  · rintro ⟨c, hc, h⟩ i j
    rw [hsq] at h
    have hk : ∀ k, Real.exp (-((β + β) * E k) / 2) = c := fun k => by
      have := congrFun (congrFun h k) k
      rw [thermal, diagonal_apply_eq, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at this
      exact_mod_cast this
    have h4 := Real.exp_injective ((hk i).trans (hk j).symm)
    have : β * E i = β * E j := by linarith
    exact mul_left_cancel₀ hβ.ne' this
  · intro hE
    obtain ⟨i₀⟩ := (inferInstance : Nonempty n)
    refine ⟨Real.exp (-((β + β) * E i₀) / 2), Real.exp_pos _, ?_⟩
    rw [hsq, thermal, ← diagonal_one, ← diagonal_smul]
    congr 1
    funext i
    simp [hE i i₀]

/-- Regression guard: Chain Theory's link, the identity, satisfies the matching hypothesis of the no-go. -/
theorem matching_invariant_one : ∀ U ∈ unitaryGroup n ℂ, U * (1 : Matrix n n ℂ) * star U = 1 :=
  fun U hU => by rw [Matrix.mul_one, mem_unitaryGroup_iff.1 hU]

/-- Regression guard: a two-level thermal link has genuine dynamics. Its transfer operator is not a multiple
of the identity, so the converse direction of `thermal_flat_iff` is not vacuous. -/
theorem two_level_not_flat : ¬ ∃ c : ℂ, ∀ B, transfer (thermal 1 ![0, 1]) B = c • B := by
  rw [thermal_flat_iff one_pos]
  intro h
  have := h 0 1
  norm_num at this

end ChainThermal

end -- public section

#print axioms ChainThermal.join_pairOf
#print axioms ChainThermal.insert_vec
#print axioms ChainThermal.join_insert
#print axioms ChainThermal.chain_eq_pow
#print axioms ChainThermal.eq_smul_one_of_matching_invariant
#print axioms ChainThermal.thermal_zero
#print axioms ChainThermal.thermal_pow
#print axioms ChainThermal.chain_thermal
#print axioms ChainThermal.isGram_thermal
#print axioms ChainThermal.thermal_rp
#print axioms ChainThermal.transfer_iterate
#print axioms ChainThermal.kron_mulVec_vec
#print axioms ChainThermal.corr_eq_trace
#print axioms ChainThermal.corr_pow
#print axioms ChainThermal.transfer_thermal_single
#print axioms ChainThermal.transfer_of_matching_invariant
#print axioms ChainThermal.eq_smul_one_of_isGram_of_maxEntangled
#print axioms ChainThermal.thermal_flat_iff
#print axioms ChainThermal.thermal_maxEntangled_iff
#print axioms ChainThermal.matching_invariant_one
#print axioms ChainThermal.two_level_not_flat

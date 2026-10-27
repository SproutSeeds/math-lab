module

/-
NormalFamily.lean

Two facts about commuting normal matrices.

  * **Fuglede's theorem** in finite dimensions (`fuglede`): if `A` commutes with a normal `N`, it commutes
    with `Nᴴ`. In an eigenbasis of `N`, `A` has no entries between distinct eigenvalues.
  * **Simultaneous diagonalization** (`normal_spectral_family`): a family of normal matrices that commute
    with each other and with each other's adjoints is `U Dₐ Uᴴ` for one unitary `U`. As in
    `normal_spectral`, the Hermitian parts `Hₐ = (Nₐ + Nₐᴴ)/2` and `Kₐ = (Nₐ - Nₐᴴ)/(2i)` commute, and an
    orthonormal basis subordinate to their joint eigenspaces diagonalizes every `Nₐ`.
-/
public import MathLab.Positivity.NormalSpectral

@[expose] public section

open Matrix

noncomputable section

namespace MathLab

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Fuglede's theorem** (finite dimensions): if `A` commutes with a normal `N`, then `A` commutes with
`Nᴴ`. -/
theorem fuglede {N A : Matrix ι ι ℂ} (hN : Nᴴ * N = N * Nᴴ) (hA : A * N = N * A) :
    A * Nᴴ = Nᴴ * A := by
  obtain ⟨U, d, hUU, hUU', rfl⟩ := normal_spectral N hN
  set X := Uᴴ * A * U with hX
  have hXD : X * diagonal d = diagonal d * X := by
    have h := congrArg (fun M => Uᴴ * M * U) hA
    simp only [Matrix.mul_assoc] at h
    calc X * diagonal d = Uᴴ * (A * (U * (diagonal d * (Uᴴ * U)))) := by
            rw [hUU, Matrix.mul_one, hX]; simp only [Matrix.mul_assoc]
      _ = Uᴴ * (U * (diagonal d * (Uᴴ * (A * U)))) := h
      _ = diagonal d * X := by
            rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, hX]; simp only [Matrix.mul_assoc]
  have hXD' : X * diagonal (star d) = diagonal (star d) * X := by
    ext i j
    have h := congrFun (congrFun hXD i) j
    rw [mul_diagonal, diagonal_mul] at h
    rw [mul_diagonal, diagonal_mul]
    by_cases hij : d i = d j
    · simp [hij, mul_comm]
    · have hx : X i j = 0 := by
        have : X i j * (d j - d i) = 0 := by linear_combination h
        exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 (Ne.symm hij))
      simp [hx]
  have hNH : (U * diagonal d * Uᴴ)ᴴ = U * diagonal (star d) * Uᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
      Matrix.mul_assoc]
  have hA' : A = U * X * Uᴴ := by
    rw [hX, ← Matrix.mul_assoc U, ← Matrix.mul_assoc U, hUU', Matrix.one_mul, Matrix.mul_assoc, hUU',
      Matrix.mul_one]
  rw [hNH, hA']
  calc U * X * Uᴴ * (U * diagonal (star d) * Uᴴ) = U * (X * diagonal (star d)) * Uᴴ := by
        simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul]
    _ = U * (diagonal (star d) * X) * Uᴴ := by rw [hXD']
    _ = U * diagonal (star d) * Uᴴ * (U * X * Uᴴ) := by
        simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul]

/-- **Simultaneous diagonalization of commuting normal matrices**: if the matrices `N a` commute with each
other and with each other's adjoints, one unitary `U` diagonalizes all of them. -/
theorem normal_spectral_family {κ : Type*} [Fintype κ] (N : κ → Matrix ι ι ℂ)
    (h1 : ∀ a b, N a * N b = N b * N a) (h2 : ∀ a b, (N a)ᴴ * N b = N b * (N a)ᴴ) :
    ∃ (U : Matrix ι ι ℂ) (d : κ → ι → ℂ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ a, N a = U * diagonal (d a) * Uᴴ := by
  classical
  have h3 : ∀ a b, N a * (N b)ᴴ = (N b)ᴴ * N a := fun a b => (h2 b a).symm
  have h4 : ∀ a b, (N a)ᴴ * (N b)ᴴ = (N b)ᴴ * (N a)ᴴ := fun a b => by
    have := congrArg conjTranspose (h1 b a)
    rwa [conjTranspose_mul, conjTranspose_mul] at this
  set Hm : κ → Matrix ι ι ℂ := fun a => (1 / 2 : ℂ) • (N a + (N a)ᴴ) with hHm
  set Km : κ → Matrix ι ι ℂ := fun a => (-Complex.I / 2) • (N a - (N a)ᴴ) with hKm
  have hHmH : ∀ a, (Hm a).IsHermitian := fun a => by
    rw [IsHermitian, hHm, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
    congr 1
    simp
  have hKmH : ∀ a, (Km a).IsHermitian := fun a => by
    rw [IsHermitian, hKm, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    have hs : star (-Complex.I / 2) = -(-Complex.I / 2) := by
      apply Complex.ext <;> norm_num
    rw [hs, neg_smul, ← smul_neg, neg_sub]
  have hsum : ∀ a, N a = Hm a + Complex.I • Km a := fun a => by
    rw [hHm, hKm, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  -- the four products commute
  have cpp : ∀ a b, (N a + (N a)ᴴ) * (N b + (N b)ᴴ) = (N b + (N b)ᴴ) * (N a + (N a)ᴴ) := fun a b => by
    simp only [add_mul, mul_add]
    rw [h1 a b, h2 a b, h3 a b, h4 a b]
    abel
  have cpm : ∀ a b, (N a + (N a)ᴴ) * (N b - (N b)ᴴ) = (N b - (N b)ᴴ) * (N a + (N a)ᴴ) := fun a b => by
    simp only [add_mul, mul_add, sub_mul, mul_sub]
    rw [h1 a b, h2 a b, h3 a b, h4 a b]
    abel
  have cmm : ∀ a b, (N a - (N a)ᴴ) * (N b - (N b)ᴴ) = (N b - (N b)ᴴ) * (N a - (N a)ᴴ) := fun a b => by
    simp only [sub_mul, mul_sub]
    rw [h1 a b, h2 a b, h3 a b, h4 a b]
    abel
  set T : κ ⊕ κ → Matrix ι ι ℂ := Sum.elim Hm Km with hT
  have hTH : ∀ j, (T j).IsHermitian := by
    rintro (a | a)
    · exact hHmH a
    · exact hKmH a
  have hTc : ∀ i j, T i * T j = T j * T i := by
    rintro (a | a) (b | b) <;>
      simp only [hT, Sum.elim_inl, Sum.elim_inr, hHm, hKm, smul_mul_smul_comm, cpp, cpm, cmm, mul_comm]
  clear_value Hm Km T
  set L : κ ⊕ κ → Module.End ℂ (EuclideanSpace ℂ ι) := fun j => toEuclideanLin (T j) with hL
  have hLs : ∀ j, (L j).IsSymmetric := fun j => isSymmetric_toEuclideanLin_iff.2 (hTH j)
  have hLc : Pairwise (Function.onFun Commute L) := fun i j _ => by
    show L i * L j = L j * L i
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, hL, ← toLpLin_mul_same, ← toLpLin_mul_same, hTc]
  have hint := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hLs hLc
  have horth := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hLs
  set V : (κ ⊕ κ → ℂ) → Submodule ℂ (EuclideanSpace ℂ ι) :=
    fun α => ⨅ j, Module.End.eigenspace (L j) (α j) with hV
  let : Fintype {α // V α ≠ ⊥} := hint.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hint' : DirectSum.IsInternal fun α : {α // V α ≠ ⊥} => V α :=
    DirectSum.isInternal_ne_bot_iff.2 hint
  have horth' := horth.comp (f := fun α : {α // V α ≠ ⊥} => α.1) Subtype.val_injective
  set b₀ := hint'.subordinateOrthonormalBasis finrank_euclideanSpace horth' with hb₀
  set b := b₀.reindex (Fintype.equivFin ι).symm with hb
  have heig : ∀ i, ∃ α : κ ⊕ κ → ℂ, ∀ j, L j (b i) = α j • b i := by
    intro i
    have hm := hint'.subordinateOrthonormalBasis_subordinate finrank_euclideanSpace
      ((Fintype.equivFin ι) i) horth'
    have hbi : b i = b₀ ((Fintype.equivFin ι) i) := by
      rw [hb, OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    rw [hbi]
    refine ⟨_, fun j => Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hm j)⟩
  choose α hα using heig
  set d : κ → ι → ℂ := fun a i => α i (Sum.inl a) + Complex.I * α i (Sum.inr a) with hd
  have hTb : ∀ j i, T j *ᵥ (b i).ofLp = α i j • (b i).ofLp := fun j i => by
    have := congrArg WithLp.ofLp (hα i j)
    simpa [hL, toLpLin_apply] using this
  have hNb : ∀ a i, N a *ᵥ (b i).ofLp = d a i • (b i).ofLp := by
    intro a i
    have hH : Hm a *ᵥ (b i).ofLp = α i (Sum.inl a) • (b i).ofLp := by
      simpa [hT] using hTb (Sum.inl a) i
    have hK : Km a *ᵥ (b i).ofLp = α i (Sum.inr a) • (b i).ofLp := by
      simpa [hT] using hTb (Sum.inr a) i
    rw [hsum, add_mulVec, smul_mulVec, hH, hK, smul_smul, hd, add_smul]
  set U : Matrix ι ι ℂ := Matrix.of fun i j => (b j).ofLp i with hU
  have hUU : Uᴴ * U = 1 := by
    ext j k
    have h := (orthonormal_iff_ite.1 b.orthonormal) j k
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    simp only [hU, conjTranspose_apply, Matrix.of_apply, dotProduct, Pi.star_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hUU
  refine ⟨U, d, hUU, hUU', fun a => ?_⟩
  have hNU : N a * U = U * diagonal (d a) := by
    ext i j
    rw [mul_diagonal]
    have := congrFun (hNb a j) i
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, hU, Matrix.of_apply, this]
    ring
  calc N a = N a * (U * Uᴴ) := by rw [hUU', Matrix.mul_one]
    _ = U * diagonal (d a) * Uᴴ := by rw [← Matrix.mul_assoc, hNU]

end MathLab

end

end -- public section

#print axioms MathLab.fuglede
#print axioms MathLab.normal_spectral_family

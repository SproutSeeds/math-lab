module

/-
LowRank.lean

**PPT states of low rank on ℂ² ⊗ ℂᵐ are separable** (Kraus, Cirac, Karnas and Lewenstein, Phys. Rev. A
61 (2000) 062302). Write ρ_B = ρ₀₀ + ρ₁₁ for the reduced operator of ρ on ℂᵐ. For a PPT operator ρ on
ℂ² ⊗ ℂᵐ:
  * rank ρ_B ≤ rank ρ (`rank_redB_le`);
  * if rank ρ ≤ rank ρ_B, so that the two ranks are equal, ρ is separable (`sep_of_rank_le_rank_redB`).
In particular a PPT operator of rank m whose ρ_B is invertible is separable (`sep_of_rank_le`).

  Part 1  The corner form `[[1, B], [Bᴴ, C]]` has rank at least m, and rank m forces `C = Bᴴ B`. With
          PPT, B is then normal, and the operator is separable.
  Part 2  When ρ_B is invertible, a shear makes the corner block invertible (`exists_shear`) and a
          local operation normalizes it to 1. Local operations do not raise the rank.
  Part 3  When ρ_B has a kernel vector w, ρ lives on ℂ² ⊗ w^⊥ (`exists_compress`); induct on m.
  Part 4  The rank condition is sharp: P. Horodecki's PPT entangled state on ℂ² ⊗ ℂ⁴ has rank 5 and its
          ρ_B has rank 4 (`rho24M_sharp`).
-/
public import MathLab.ChainTheory.PPTCriterion

@[expose] public section

open Matrix ComplexOrder Module
open scoped Kronecker

noncomputable section

namespace ChainLowRank

open ChoiDark ChainReadCap ChainDuality ChainWoronowicz ChainPPT

variable {m : ℕ}

/-- The reduced operator on the second factor, `ρ_B = ρ₀₀ + ρ₁₁`. -/
def redB (ρ : Mat 2 m) : Matrix (Fin m) (Fin m) ℂ := blkOf ρ 0 0 + blkOf ρ 1 1

/-! ## Part 1. The corner form -/

/-- The first block column of `[[1, B], [Bᴴ, C]]`: `u ↦ (u, Bᴴ u)`. -/
def cornerCol (B : Matrix (Fin m) (Fin m) ℂ) : (Fin m → ℂ) →ₗ[ℂ] (Idx 2 m → ℂ) where
  toFun u := bvec u (Bᴴ *ᵥ u)
  map_add' u v := by
    ext ⟨a, k⟩
    fin_cases a <;> simp [bvec, mulVec_add]
  map_smul' c u := by
    ext ⟨a, k⟩
    fin_cases a <;> simp [bvec, mulVec_smul]

theorem cornerCol_injective (B : Matrix (Fin m) (Fin m) ℂ) : Function.Injective (cornerCol B) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  exact (bvec_eq_zero hu).1

theorem range_cornerCol_le (B C : Matrix (Fin m) (Fin m) ℂ) :
    LinearMap.range (cornerCol B) ≤ LinearMap.range (blk 1 B Bᴴ C).mulVecLin := by
  rintro _ ⟨u, rfl⟩
  refine ⟨bvec u 0, ?_⟩
  rw [Matrix.mulVecLin_apply, blk_mulVec_bvec]
  simp [cornerCol]

theorem finrank_range_cornerCol (B : Matrix (Fin m) (Fin m) ℂ) :
    finrank ℂ (LinearMap.range (cornerCol B)) = m := by
  rw [LinearMap.finrank_range_of_inj (cornerCol_injective B), Module.finrank_fin_fun]

/-- **The corner form has rank at least m.** -/
theorem le_rank_corner (B C : Matrix (Fin m) (Fin m) ℂ) : m ≤ (blk 1 B Bᴴ C).rank := by
  have h := Submodule.finrank_mono (range_cornerCol_le B C)
  rwa [finrank_range_cornerCol] at h

/-- **Rank m forces `C = Bᴴ B`**: a nonzero Schur complement adds a vector `(0, (C - Bᴴ B) v)` outside
the first block column. -/
theorem eq_of_rank_corner_le {B C : Matrix (Fin m) (Fin m) ℂ} (h : (blk 1 B Bᴴ C).rank ≤ m) :
    C = Bᴴ * B := by
  by_contra hne
  obtain ⟨v, hv⟩ : ∃ v, (C - Bᴴ * B) *ᵥ v ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (sub_eq_zero.1 (Matrix.ext fun i j => by simpa using congrFun (hall (Pi.single j 1)) i))
  set x : Idx 2 m → ℂ := bvec 0 ((C - Bᴴ * B) *ᵥ v) with hx
  have hxR : x ∈ LinearMap.range (blk 1 B Bᴴ C).mulVecLin := by
    refine ⟨bvec (-(B *ᵥ v)) v, ?_⟩
    rw [Matrix.mulVecLin_apply, blk_mulVec_bvec, hx, one_mulVec, neg_add_cancel, mulVec_neg, sub_mulVec,
      mulVec_mulVec, neg_add_eq_sub]
  have hxL : x ∉ LinearMap.range (cornerCol B) := by
    rintro ⟨u, hu⟩
    have hu0 : u = 0 := funext fun k => by simpa [cornerCol, bvec, hx] using congrFun hu (0, k)
    apply hv
    funext k
    have := congrFun hu (1, k)
    simp only [cornerCol, LinearMap.coe_mk, AddHom.coe_mk, hu0, mulVec_zero, hx, bvec] at this
    simpa using this.symm
  have hlt : LinearMap.range (cornerCol B) < LinearMap.range (cornerCol B) ⊔ (ℂ ∙ x) :=
    lt_of_le_of_ne le_sup_left fun he =>
      hxL (he ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
  have hle : LinearMap.range (cornerCol B) ⊔ (ℂ ∙ x) ≤ LinearMap.range (blk 1 B Bᴴ C).mulVecLin :=
    sup_le (range_cornerCol_le B C) ((Submodule.span_singleton_le_iff_mem _ _).2 hxR)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := Submodule.finrank_mono hle
  rw [finrank_range_cornerCol] at h1
  have h3 : finrank ℂ (LinearMap.range (blk 1 B Bᴴ C).mulVecLin) = (blk 1 B Bᴴ C).rank := rfl
  omega

/-- **A normal corner gives a separable operator**: if `B` is normal and `C ⪰ B Bᴴ`, then
`[[1, B], [Bᴴ, C]]` is separable (`sep_of_normal_dilation` with the trivial dilation). -/
theorem sep_of_normal {B C : Matrix (Fin m) (Fin m) ℂ} (hB : Bᴴ * B = B * Bᴴ)
    (hC : IsPSD (C - B * Bᴴ)) : IsSeparable (blk 1 B Bᴴ C) := by
  set N : Matrix (Fin m ⊕ Fin 0) (Fin m ⊕ Fin 0) ℂ := fromBlocks B 0 0 0 with hNdef
  have hN : Nᴴ * N = N * Nᴴ := by
    rw [hNdef, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [hB]
  have hNN : (N * Nᴴ).toBlocks₁₁ = B * Bᴴ := by
    rw [hNdef, fromBlocks_conjTranspose, fromBlocks_multiply]
    simp
  have := sep_of_normal_dilation N hN C (by rw [hNN]; exact hC)
  rwa [hNdef, toBlocks_fromBlocks₁₁] at this

/-- **A PPT corner form of rank m is separable**: `C = Bᴴ B`, and PPT gives `C ⪰ B Bᴴ`, so `Bᴴ B - B Bᴴ`
is positive with trace zero and `B` is normal. -/
theorem sep_of_corner_rank {B C : Matrix (Fin m) (Fin m) ℂ} (hρ : IsPPT (blk 1 B Bᴴ C))
    (hr : (blk 1 B Bᴴ C).rank ≤ m) : IsSeparable (blk 1 B Bᴴ C) := by
  have hC := eq_of_rank_corner_le hr
  have hS' := isPSD_of_transpose (isPSD_schur_pt hρ.2)
  have hN : Bᴴ * B - B * Bᴴ = 0 := by
    apply eq_zero_of_isPSD_trace
    · rwa [hC] at hS'
    · rw [trace_sub, trace_mul_comm, sub_self]
  exact sep_of_normal (sub_eq_zero.1 hN) hS'

/-! ## Part 2. When ρ_B is invertible -/

/-- Local operations do not raise the rank. -/
theorem rank_lop_le {n n' m' : ℕ} (G : Matrix (Fin n') (Fin n) ℂ) (M : Matrix (Fin m') (Fin m) ℂ)
    (ρ : Mat n m) : (lop G M ρ).rank ≤ ρ.rank :=
  (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- **Normal form**: when ρ is PPT and ρ_B is invertible, an invertible local operation brings ρ to the
corner form `[[1, B], [Bᴴ, C]]`. A shear makes the corner block invertible, and `1 ⊗ (Fᴴ)⁻¹`, for a
Gram factor `F` of that block, makes it 1. -/
theorem exists_corner_form {ρ : Mat 2 m} (hρ : IsPPT ρ) (hB : (redB ρ).det ≠ 0) :
    ∃ (G G' : Matrix (Fin 2) (Fin 2) ℂ) (M M' : Matrix (Fin m) (Fin m) ℂ)
      (B C : Matrix (Fin m) (Fin m) ℂ), lop G M ρ = blk 1 B Bᴴ C ∧ lop G' M' (lop G M ρ) = ρ := by
  have hH : ρᴴ = ρ := hρ.1.hermitian
  have h10 := blkOf_10_of_hermitian hH
  have hρblk : ρ = blk (blkOf ρ 0 0) (blkOf ρ 0 1) (blkOf ρ 0 1)ᴴ (blkOf ρ 1 1) := by
    rw [← h10]
    exact (blk_blkOf ρ).symm
  obtain ⟨z, hz⟩ := exists_shear (hρblk ▸ hρ) hB
  set G : Matrix (Fin 2) (Fin 2) ℂ := !![(1 : ℂ), (z : ℂ); 0, 1] with hG
  have hGG : !![(1 : ℂ), -(z : ℂ); 0, 1] * G = 1 := shear_mul_inv _
  have h00 : blkOf (lop G (1 : Matrix (Fin m) (Fin m) ℂ) ρ) 0 0 = blkOf ρ 0 0 +
      star (z : ℂ) • blkOf ρ 0 1 + (z : ℂ) • (blkOf ρ 0 1)ᴴ + ((z : ℂ) * star (z : ℂ)) • blkOf ρ 1 1 := by
    rw [hG, blkOf_lop_shear, h10]
  have hpsd : IsPSD (blkOf (lop G (1 : Matrix (Fin m) (Fin m) ℂ) ρ) 0 0) :=
    isPSD_blkOf_00 (isPSD_lop _ _ hρ.1)
  obtain ⟨F, hF⟩ := hpsd.gram
  have hFdet : IsUnit F.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hz
    rw [← h00, hF, det_mul, det_conjTranspose, h0, mul_zero]
  have hFHdet : IsUnit Fᴴ.det := by
    rw [det_conjTranspose]
    exact hFdet.star
  set M : Matrix (Fin m) (Fin m) ℂ := (Fᴴ)⁻¹ with hM
  have hMM : Fᴴ * M = 1 := mul_nonsing_inv _ hFHdet
  have hMM' : M * Fᴴ = 1 := nonsing_inv_mul _ hFHdet
  have hρ₂ : lop (1 : Matrix (Fin 2) (Fin 2) ℂ) M (lop G (1 : Matrix (Fin m) (Fin m) ℂ) ρ) =
      lop G M ρ := by
    rw [lop_lop, Matrix.one_mul, Matrix.mul_one]
  have h00' : blkOf (lop G M ρ) 0 0 = 1 := by
    rw [← hρ₂, blkOf_lop_one, hF]
    have hMH : Mᴴ = F⁻¹ := by rw [hM, conjTranspose_nonsing_inv, conjTranspose_conjTranspose]
    rw [hMH, ← Matrix.mul_assoc, hMM', Matrix.one_mul, mul_nonsing_inv _ hFdet]
  have hform : lop G M ρ = blk 1 (blkOf (lop G M ρ) 0 1) (blkOf (lop G M ρ) 0 1)ᴴ
      (blkOf (lop G M ρ) 1 1) := by
    rw [← h00', ← blkOf_10_of_hermitian (isPSD_lop G M hρ.1).hermitian]
    exact (blk_blkOf _).symm
  refine ⟨G, !![(1 : ℂ), -(z : ℂ); 0, 1], M, Fᴴ, _, _, hform, ?_⟩
  rw [lop_lop, hGG, hMM, lop_one]

/-- **A PPT operator on `ℂ² ⊗ ℂᵐ` whose ρ_B is invertible has rank at least m.** -/
theorem le_rank_of_det_ne_zero {ρ : Mat 2 m} (hρ : IsPPT ρ) (hB : (redB ρ).det ≠ 0) : m ≤ ρ.rank := by
  obtain ⟨G, -, M, -, B, C, h1, -⟩ := exists_corner_form hρ hB
  have h := le_rank_corner B C
  rw [← h1] at h
  exact h.trans (rank_lop_le G M ρ)

/-- **Kraus, Cirac, Karnas and Lewenstein**: a PPT operator on `ℂ² ⊗ ℂᵐ` of rank at most m whose ρ_B is
invertible is separable. -/
theorem sep_of_rank_le {ρ : Mat 2 m} (hρ : IsPPT ρ) (hB : (redB ρ).det ≠ 0) (hr : ρ.rank ≤ m) :
    IsSeparable ρ := by
  obtain ⟨G, G', M, M', B, C, h1, h2⟩ := exists_corner_form hρ hB
  have hppt : IsPPT (blk 1 B Bᴴ C) := h1 ▸ isPPT_lop G M hρ
  have hrank : (blk 1 B Bᴴ C).rank ≤ m := h1 ▸ (rank_lop_le G M ρ).trans hr
  rw [← h2, h1]
  exact isSeparable_lop _ _ (sep_of_corner_rank hppt hrank)

/-! ## Part 3. When ρ_B is singular -/

theorem redB_lop_one {m' : ℕ} (M : Matrix (Fin m') (Fin m) ℂ) (ρ : Mat 2 m) :
    redB (lop (1 : Matrix (Fin 2) (Fin 2) ℂ) M ρ) = M * redB ρ * Mᴴ := by
  rw [redB, redB, blkOf_lop_one, blkOf_lop_one, Matrix.mul_add, Matrix.add_mul]

theorem rank_redB_lop_one_le {m' : ℕ} (M : Matrix (Fin m') (Fin m) ℂ) (ρ : Mat 2 m) :
    (redB (lop (1 : Matrix (Fin 2) (Fin 2) ℂ) M ρ)).rank ≤ (redB ρ).rank := by
  rw [redB_lop_one]
  exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

theorem eq_zero_of_mat_two_zero (ρ : Mat 2 0) : ρ = 0 := by
  ext ⟨_, k⟩
  exact k.elim0

/-- **A PPT operator on `ℂ² ⊗ ℂᵐ` has rank at least that of ρ_B.** -/
theorem rank_redB_le : ∀ {m : ℕ} {ρ : Mat 2 m}, IsPPT ρ → (redB ρ).rank ≤ ρ.rank := by
  intro m
  induction m with
  | zero => exact fun _ => (rank_le_width _).trans (Nat.zero_le _)
  | succ k ih =>
    intro ρ hρ
    by_cases hB : (redB ρ).det = 0
    · obtain ⟨w, hw, hw0⟩ := exists_mulVec_eq_zero_iff.2 hB
      obtain ⟨V, hV⟩ := exists_compress hρ.1 hw hw0
      have hσ := isPPT_lop (1 : Matrix (Fin 2) (Fin 2) ℂ) Vᴴ hρ
      calc (redB ρ).rank
          = (redB (lop (1 : Matrix (Fin 2) (Fin 2) ℂ) V (lop 1 Vᴴ ρ))).rank := by rw [hV]
        _ ≤ (redB (lop (1 : Matrix (Fin 2) (Fin 2) ℂ) Vᴴ ρ)).rank := rank_redB_lop_one_le _ _
        _ ≤ (lop (1 : Matrix (Fin 2) (Fin 2) ℂ) Vᴴ ρ).rank := ih hσ
        _ ≤ ρ.rank := rank_lop_le _ _ _
    · exact (rank_le_width _).trans (le_rank_of_det_ne_zero hρ hB)

/-- **The 2 × m low-rank theorem**: a PPT operator on `ℂ² ⊗ ℂᵐ` whose rank is at most that of ρ_B, so
equal to it by `rank_redB_le`, is separable. When ρ_B is singular, ρ lives on `ℂ² ⊗ w^⊥` for a kernel
vector w, with the same rank and the same rank of ρ_B; induct on m. -/
theorem sep_of_rank_le_rank_redB :
    ∀ {m : ℕ} {ρ : Mat 2 m}, IsPPT ρ → ρ.rank ≤ (redB ρ).rank → IsSeparable ρ := by
  intro m
  induction m with
  | zero =>
    intro ρ _ _
    rw [eq_zero_of_mat_two_zero ρ]
    exact isSeparable_zero
  | succ k ih =>
    intro ρ hρ hr
    by_cases hB : (redB ρ).det = 0
    · obtain ⟨w, hw, hw0⟩ := exists_mulVec_eq_zero_iff.2 hB
      obtain ⟨V, hV⟩ := exists_compress hρ.1 hw hw0
      have hσ := isPPT_lop (1 : Matrix (Fin 2) (Fin 2) ℂ) Vᴴ hρ
      have hrσ : (lop (1 : Matrix (Fin 2) (Fin 2) ℂ) Vᴴ ρ).rank ≤
          (redB (lop (1 : Matrix (Fin 2) (Fin 2) ℂ) Vᴴ ρ)).rank :=
        calc (lop (1 : Matrix (Fin 2) (Fin 2) ℂ) Vᴴ ρ).rank ≤ ρ.rank := rank_lop_le _ _ _
          _ ≤ (redB ρ).rank := hr
          _ = (redB (lop (1 : Matrix (Fin 2) (Fin 2) ℂ) V (lop 1 Vᴴ ρ))).rank := by rw [hV]
          _ ≤ (redB (lop (1 : Matrix (Fin 2) (Fin 2) ℂ) Vᴴ ρ)).rank := rank_redB_lop_one_le _ _
      rw [← hV]
      exact isSeparable_lop _ _ (ih hσ hrσ)
    · exact sep_of_rank_le hρ hB (hr.trans (rank_le_width _))

/-- **Separable exactly at the rank of ρ_B**: a PPT operator on `ℂ² ⊗ ℂᵐ` with the same rank as its
reduced operator ρ_B is separable. -/
theorem sep_of_rank_eq {ρ : Mat 2 m} (hρ : IsPPT ρ) (hr : ρ.rank = (redB ρ).rank) : IsSeparable ρ :=
  sep_of_rank_le_rank_redB hρ hr.le

/-! ## Part 4. The rank condition is sharp -/

theorem rho24_redB_table : ∀ k l : Fin 4, rho24 0 k 0 l + rho24 1 k 1 l =
    (![![7 / 26, 0, 0, 2 / 26], ![0, 6 / 26, 0, 0], ![0, 0, 6 / 26, 0], ![2 / 26, 0, 0, 7 / 26]] :
      Fin 4 → Fin 4 → ℚ) k l := by
  decide +kernel

/-- ρ_B of the Horodecki state. -/
theorem redB_rho24M : redB rho24M =
    !![(7 / 26 : ℂ), 0, 0, 2 / 26; 0, 6 / 26, 0, 0; 0, 0, 6 / 26, 0; 2 / 26, 0, 0, 7 / 26] := by
  ext k l
  have h := congrArg (fun q : ℚ => (q : ℂ)) (rho24_redB_table k l)
  push_cast at h
  simp only [redB, Matrix.add_apply, blkOf, rho24M]
  rw [h]
  fin_cases k <;> fin_cases l <;> simp

/-- ρ_B of the Horodecki state is invertible: an explicit inverse. -/
theorem det_redB_rho24M : (redB rho24M).det ≠ 0 := by
  have hinv : redB rho24M *
      !![(7 * 26 / 45 : ℂ), 0, 0, -2 * 26 / 45; 0, 26 / 6, 0, 0; 0, 0, 26 / 6, 0;
        -2 * 26 / 45, 0, 0, 7 * 26 / 45] = 1 := by
    rw [redB_rho24M]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  exact (isUnit_det_of_right_inverse hinv).ne_zero

theorem rank_rho24M_le : rho24M.rank ≤ 5 := by
  set V : Matrix (Idx 2 4) (Fin 5) ℂ := of fun x j => (rho24Vec j (ix x.1 x.2) : ℂ) with hV
  have e : rho24M = V * diagonal (fun j => (rho24Wt j : ℂ)) * Vᵀ := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [mul_diagonal, transpose_apply, hV, of_apply, rho24M, rho24]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact (rank_mul_le_left _ _).trans ((rank_mul_le_left _ _).trans ((rank_le_card_width V).trans (by simp)))

/-- **The rank condition is sharp**: P. Horodecki's state on `ℂ² ⊗ ℂ⁴` is PPT and entangled, its ρ_B has
rank 4, and its own rank is 5. That it has rank at least 5 follows from `sep_of_rank_le_rank_redB`. -/
theorem rho24M_sharp :
    IsPPT rho24M ∧ ¬ IsSeparable rho24M ∧ (redB rho24M).rank = 4 ∧ rho24M.rank = 5 := by
  obtain ⟨hppt, hent⟩ := rho24M_ppt_entangled
  have hB : (redB rho24M).rank = 4 := by
    rw [rank_of_det_ne_zero det_redB_rho24M, Fintype.card_fin]
  refine ⟨hppt, hent, hB, le_antisymm rank_rho24M_le ?_⟩
  by_contra hlt
  push Not at hlt
  exact hent (sep_of_rank_le_rank_redB hppt (by omega))

end ChainLowRank

end

end -- public section

#print axioms ChainLowRank.eq_of_rank_corner_le
#print axioms ChainLowRank.sep_of_normal
#print axioms ChainLowRank.exists_corner_form
#print axioms ChainLowRank.sep_of_rank_le
#print axioms ChainLowRank.rank_redB_le
#print axioms ChainLowRank.sep_of_rank_le_rank_redB
#print axioms ChainLowRank.sep_of_rank_eq
#print axioms ChainLowRank.rho24M_sharp

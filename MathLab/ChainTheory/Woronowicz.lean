module

/-
Woronowicz.lean

**Woronowicz's theorem** (S. L. Woronowicz, Rep. Math. Phys. 10 (1976) 165): every positive linear
map M₂(ℂ) → M₃(ℂ) is decomposable. With it the alpha Letter's read cap holds for its own readability
with no hypothesis (`readcap`).

The proof is in state form and follows Kaliuzhnyi-Verbovetskyi, Spitkovsky and Woerdeman, Oper.
Matrices 3 (2009), Thm 5.2, with Krein–Milman in place of their extreme-ray decomposition:
  1. On an extreme ray of the PPT cone of ℂ² ⊗ ℂ³, `r² + s² ≤ 37` for the ranks of ρ and ρ^Γ
     (`PPTFace.lean`).
  2. If the reduced operator on ℂ³ is singular, ρ lives on ℂ² ⊗ ℂ² and is separable by the two-qubit
     theorem (Physical Superintelligence's `twoQubit_ppt_separable`, through `Stormer.lean`).
  3. Otherwise a local operation brings ρ to `[[1, B], [Bᴴ, C]]`. The bound leaves three cases:
     `C = BᴴB`, `C = BBᴴ`, or both Schur complements of rank one. In each, B has a normal dilation N
     with `C ⪰ (N Nᴴ)₁₁` (`NormalCompletion.lean`, KSW Thm 2.4 in the third case), and then ρ is
     separable (`sep_of_normal_dilation`).
  4. Krein–Milman: the trace-one PPT operators are the closed convex hull of their extreme points, so
     every PPT operator pairs nonnegatively with the Choi matrix of every positive map, and the
     separation argument of `Duality.lean` gives decomposability.
-/
public import MathLab.ChainTheory.PPTFace
public import Mathlib.Analysis.Convex.KreinMilman

@[expose] public section

open Matrix ComplexOrder Module
open scoped Kronecker

noncomputable section

namespace ChainWoronowicz

open ChoiDark ChainReadCap ChainDuality ChainStormer

variable {m : ℕ}

/-! ## Positive matrices -/

theorem isPSD_mulVec_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ}
    (hP : IsPSD P) {v : ι → ℂ} (h : star v ⬝ᵥ (P *ᵥ v) = 0) : P *ᵥ v = 0 := by
  obtain ⟨F, rfl⟩ := hP.gram
  have h1 : star (F *ᵥ v) ⬝ᵥ (F *ᵥ v) = 0 := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
    exact h
  rw [← mulVec_mulVec, dotProduct_star_self_eq_zero.1 h1, mulVec_zero]

theorem isPSD_transpose {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ} (h : IsPSD M) : IsPSD Mᵀ := by
  intro w
  have e : star w ⬝ᵥ (Mᵀ *ᵥ w) = star (star w) ⬝ᵥ (M *ᵥ star w) := by
    simp only [dotProduct, mulVec, transpose_apply, star_star, Pi.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  exact h _

theorem isPSD_of_transpose {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ} (h : IsPSD Mᵀ) : IsPSD M := by
  simpa using isPSD_transpose h

theorem eq_zero_of_isPSD_trace {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (h : IsPSD M) (htr : M.trace = 0) : M = 0 := by
  obtain ⟨F, rfl⟩ := h.gram
  rw [trace_conjTranspose_mul_self_eq_zero_iff.1 htr, Matrix.mul_zero]

/-- The Schur complement of `[[1, B], [Bᴴ, C]] ⪰ 0` is `C - Bᴴ B ⪰ 0`. -/
theorem isPSD_schur {B C : Matrix (Fin m) (Fin m) ℂ} (h : IsPSD (blk 1 B Bᴴ C)) :
    IsPSD (C - Bᴴ * B) := by
  intro w
  have e : star w ⬝ᵥ ((C - Bᴴ * B) *ᵥ w) =
      star (bvec (-(B *ᵥ w)) w) ⬝ᵥ (blk 1 B Bᴴ C *ᵥ bvec (-(B *ᵥ w)) w) := by
    rw [blk_mulVec_bvec, star_bvec_dotProduct, one_mulVec, neg_add_cancel, dotProduct_zero,
      zero_add, mulVec_neg, mulVec_mulVec, sub_mulVec, neg_add_eq_sub]
  rw [e]
  exact h _

theorem conjTranspose_transpose' (B : Matrix (Fin m) (Fin m) ℂ) : (Bᵀ)ᴴ = (Bᴴ)ᵀ := rfl

/-- The Schur complement of the partial transpose: `(C - B Bᴴ)ᵀ ⪰ 0`. -/
theorem isPSD_schur_pt {B C : Matrix (Fin m) (Fin m) ℂ} (h : IsPSD (pt (blk 1 B Bᴴ C))) :
    IsPSD (C - B * Bᴴ)ᵀ := by
  rw [pt_blk, transpose_one, ← conjTranspose_transpose'] at h
  have h2 := isPSD_schur h
  rwa [conjTranspose_transpose', ← transpose_mul, ← transpose_sub] at h2

/-- A Gram factor `S = Gᴴ G`, a basis `b` of the range of `Gᴴ`, and what its size says about `S`. -/
theorem psd_basis {S : Matrix (Fin m) (Fin m) ℂ} (hS : IsPSD S) :
    ∃ (G : Matrix (Fin m) (Fin m) ℂ) (k : ℕ) (b : Fin k → Fin m → ℂ), S = Gᴴ * G ∧
      LinearIndependent ℂ b ∧ (∀ j, ∃ c, b j = Gᴴ *ᵥ c) ∧ (k = 0 → S = 0) ∧
      (k = 1 → ∃ y, S = vecMulVec y (star y)) := by
  obtain ⟨G, hG⟩ := hS.gram
  set R := LinearMap.range (Gᴴ).mulVecLin with hR
  set bas := Module.finBasis ℂ R with hbas
  have hcol : ∀ j, Gᴴ *ᵥ Pi.single j 1 ∈ R := fun j => LinearMap.mem_range_self _ _
  have hGG : S = Gᴴ * (Gᴴ)ᴴ := by rw [conjTranspose_conjTranspose, hG]
  refine ⟨G, finrank ℂ R, fun j => (bas j : Fin m → ℂ), hG, ?_, ?_, ?_, ?_⟩
  · exact bas.linearIndependent.map' R.subtype (Submodule.ker_subtype R)
  · intro j
    obtain ⟨c, hc⟩ := (bas j).2
    exact ⟨c, hc.symm⟩
  · intro hk
    have hR0 : R = ⊥ := Submodule.finrank_eq_zero.1 hk
    have hGH : Gᴴ = 0 := by
      ext i j
      have h := hcol j
      rw [hR0, Submodule.mem_bot] at h
      have := congrFun h i
      simpa [mulVec_single_one] using this
    rw [hGG, hGH, Matrix.zero_mul]
  · intro hk
    have h0 : (0 : ℕ) < finrank ℂ R := by omega
    set b0 : R := bas ⟨0, h0⟩ with hb0
    have hne : b0 ≠ 0 := bas.ne_zero _
    have hspan := (finrank_eq_one_iff_of_nonzero' b0 hne).1 hk
    have hc : ∀ j, ∃ c : ℂ, c • (b0 : Fin m → ℂ) = Gᴴ *ᵥ Pi.single j 1 := by
      intro j
      obtain ⟨c, hc⟩ := hspan ⟨_, hcol j⟩
      exact ⟨c, congrArg Subtype.val hc⟩
    choose c hc using hc
    have hGH : Gᴴ = vecMulVec (b0 : Fin m → ℂ) c := by
      ext i j
      have := congrFun (hc j) i
      simp only [Pi.smul_apply, smul_eq_mul, mulVec_single_one, col_apply] at this
      rw [vecMulVec_apply, ← this, mul_comm]
    have hcc : ((Real.sqrt (∑ j, ‖c j‖ ^ 2) : ℝ) : ℂ) * star ((Real.sqrt (∑ j, ‖c j‖ ^ 2) : ℝ) : ℂ) =
        ∑ j, c j * star (c j) := by
      rw [RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      push_cast
      exact Finset.sum_congr rfl fun j _ => (Complex.mul_conj' (c j)).symm
    refine ⟨((Real.sqrt (∑ j, ‖c j‖ ^ 2) : ℝ) : ℂ) • (b0 : Fin m → ℂ), ?_⟩
    rw [hGG, hGH]
    ext i l
    simp only [Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Pi.star_apply, star_mul']
    calc ∑ x, (b0 : Fin m → ℂ) i * c x * (star ((b0 : Fin m → ℂ) l) * star (c x))
        = (b0 : Fin m → ℂ) i * star ((b0 : Fin m → ℂ) l) * ∑ x, c x * star (c x) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by rw [← hcc]; ring

/-! ## The normalized base case -/

/-- **On an extreme ray, `[[1, B], [Bᴴ, C]]` on `ℂ² ⊗ ℂ³` is separable.** -/
theorem sep_of_extreme_normalized {B C : Matrix (Fin 3) (Fin 3) ℂ}
    (hρ : IsExtremePPT (blk 1 B Bᴴ C)) : IsSeparable (blk 1 B Bᴴ C) := by
  have hS := isPSD_schur hρ.1.1
  have hS' := isPSD_schur_pt hρ.1.2
  obtain ⟨G, k, b, hG, hb, hbG, hk0, hk1⟩ := psd_basis hS
  obtain ⟨G', k', b', hG', hb', hbG', hk0', hk1'⟩ := psd_basis hS'
  -- Gram factors of ρ and of its partial transpose
  have hF : blk 1 B Bᴴ C = (blk 1 B 0 G)ᴴ * blk 1 B 0 G := by
    rw [blk_conjTranspose, blk_mul, ← hG]
    simp
  have hF' : pt (blk 1 B Bᴴ C) = (blk 1 Bᵀ 0 G')ᴴ * blk 1 Bᵀ 0 G' := by
    have e : (C - B * Bᴴ)ᵀ = Cᵀ - (Bᵀ)ᴴ * Bᵀ := by
      rw [transpose_sub, transpose_mul, conjTranspose_transpose']
    rw [pt_blk, blk_conjTranspose, blk_mul, ← hG', e]
    simp [conjTranspose_transpose']
  -- independent vectors in the ranges of the Gram factors
  set u : Fin 3 ⊕ Fin k → Idx 2 3 → ℂ :=
    Sum.elim (fun j => bvec (Pi.single j 1) (Bᴴ *ᵥ Pi.single j 1)) (fun j => bvec 0 (b j)) with hu_def
  set v : Fin 3 ⊕ Fin k' → Idx 2 3 → ℂ :=
    Sum.elim (fun j => bvec (Pi.single j 1) ((Bᵀ)ᴴ *ᵥ Pi.single j 1)) (fun j => bvec 0 (b' j))
    with hv_def
  have hind : ∀ {k : ℕ} (b : Fin k → Fin 3 → ℂ) (D : Matrix (Fin 3) (Fin 3) ℂ),
      LinearIndependent ℂ b → LinearIndependent ℂ
        (Sum.elim (fun j => bvec (Pi.single j 1) (D *ᵥ Pi.single j 1)) (fun j => bvec 0 (b j)) :
          Fin 3 ⊕ Fin k → Idx 2 3 → ℂ) := by
    intro k b D hb
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ∀ j, g (Sum.inl j) = 0 := by
      intro j
      have := congrFun hg (0, j)
      simpa [bvec, Fintype.sum_sum_type, Pi.single_apply, Finset.sum_apply] using this
    have h1 : ∑ l, g (Sum.inr l) • b l = 0 := by
      ext x
      have := congrFun hg (1, x)
      simpa [bvec, Fintype.sum_sum_type, h0, Finset.sum_apply] using this
    have h2 := Fintype.linearIndependent_iff.1 hb _ h1
    rintro (j | l)
    · exact h0 j
    · exact h2 l
  have hu' : ∀ i, ∃ w, u i = (blk 1 B 0 G)ᴴ *ᵥ w := by
    rintro (j | l)
    · exact ⟨bvec (Pi.single j 1) 0, by
        rw [blk_conjTranspose, blk_mulVec_bvec, conjTranspose_one, one_mulVec]; simp [hu_def]⟩
    · obtain ⟨c, hc⟩ := hbG l
      exact ⟨bvec 0 c, by rw [blk_conjTranspose, blk_mulVec_bvec]; simp [hu_def, hc]⟩
  have hv' : ∀ i, ∃ w, v i = (blk 1 Bᵀ 0 G')ᴴ *ᵥ w := by
    rintro (j | l)
    · exact ⟨bvec (Pi.single j 1) 0, by
        rw [blk_conjTranspose, blk_mulVec_bvec, conjTranspose_one, one_mulVec]; simp [hv_def]⟩
    · obtain ⟨c, hc⟩ := hbG' l
      exact ⟨bvec 0 c, by rw [blk_conjTranspose, blk_mulVec_bvec]; simp [hv_def, hc]⟩
  have hbound := extreme_rank_bound hρ _ _ hF hF' (u ∘ finSumFinEquiv.symm)
    ((hind b Bᴴ hb).comp _ finSumFinEquiv.symm.injective) (fun i => hu' _)
    (v ∘ finSumFinEquiv.symm) ((hind b' (Bᵀ)ᴴ hb').comp _ finSumFinEquiv.symm.injective)
    (fun i => hv' _)
  have hk : k = 0 ∨ k' = 0 ∨ (k = 1 ∧ k' = 1) := by
    have hk3 : k ≤ 3 := by nlinarith
    have hk3' : k' ≤ 3 := by nlinarith
    interval_cases k <;> interval_cases k' <;> omega
  -- in every case: C = B Bᴴ + x xᴴ and Bᴴ B - B Bᴴ = x xᴴ - y yᴴ
  obtain ⟨x, y, hC, hD⟩ : ∃ x y : Fin 3 → ℂ, C = B * Bᴴ + vecMulVec x (star x) ∧
      Bᴴ * B - B * Bᴴ = vecMulVec x (star x) - vecMulVec y (star y) := by
    rcases hk with h | h | ⟨h, h'⟩
    · have hCB : C = Bᴴ * B := sub_eq_zero.1 (hk0 h)
      have hN : Bᴴ * B - B * Bᴴ = 0 := by
        apply eq_zero_of_isPSD_trace
        · have := isPSD_of_transpose hS'
          rwa [hCB] at this
        · rw [trace_sub, trace_mul_comm, sub_self]
      refine ⟨0, 0, ?_, ?_⟩
      · rw [hCB, sub_eq_zero.1 hN]
        simp
      · rw [hN]
        simp
    · have hCB : C = B * Bᴴ := by
        have h0 : (C - B * Bᴴ)ᵀ = 0 := hk0' h
        have : C - B * Bᴴ = 0 := by
          rw [← transpose_transpose (C - B * Bᴴ), h0, transpose_zero]
        exact sub_eq_zero.1 this
      have hN : B * Bᴴ - Bᴴ * B = 0 := by
        apply eq_zero_of_isPSD_trace
        · rwa [hCB] at hS
        · rw [trace_sub, trace_mul_comm, sub_self]
      refine ⟨0, 0, ?_, ?_⟩
      · rw [hCB]
        simp
      · rw [← neg_sub, hN]
        simp
    · obtain ⟨y, hy⟩ := hk1 h
      obtain ⟨x', hx'⟩ := hk1' h'
      have hx : C - B * Bᴴ = vecMulVec (star x') (star (star x')) := by
        rw [← transpose_transpose (C - B * Bᴴ), hx']
        ext i j
        simp [vecMulVec_apply, mul_comm]
      refine ⟨star x', y, ?_, ?_⟩
      · rw [← hx]
        abel
      · rw [← hx, ← hy]
        abel
  obtain ⟨N, w, hN, hN11, hNC⟩ := MathLab.exists_normal_dilation B x y hD
  have hsep := sep_of_normal_dilation N hN C (by rw [hC, hNC]; exact isPSD_rank_one w)
  rwa [hN11] at hsep

end ChainWoronowicz

end

end -- public section

module

/-
Channels/PPTSquaredThree.lean

**PPT² on `M_3`** (Christandl, Müller-Hermes and Wolf 2019; Chen, Yang and Tang 2019): the composition of
two PPT maps on `M_3` is entanglement breaking.

  Part 1  Schmidt-number bookkeeping: sums, and families indexed by any finite type.
  Part 2  Blocks of an operator on `ℂ³ ⊗ ℂⁿ` along the reference splitting `ℂ³ = ℂ² ⊕ ℂ`.
  Part 3  The lifting lemma (Chen, Yang and Tang 2017, Lemma 15(i); Turturean and Bao 2026, Lemma 4): if
          the top block of a positive operator is separable, the operator has Schmidt number at most 2.
          A generalized Schur complement, with a pseudo-inverse built from the support of the top block.
  Part 4  Every PPT operator on `ℂ³ ⊗ ℂ³` has Schmidt number at most 2 (Yang, Leung and Tang 2016): its top
          block is PPT on `ℂ² ⊗ ℂ³`, hence separable by Woronowicz's theorem. PPT² on `M_3` follows.
-/
public import MathLab.Channels.Schmidt

@[expose] public section

open Matrix
open scoped Kronecker

noncomputable section

namespace Channels

open ChoiDark ChainDuality ChainStormer ChainWoronowicz ChainPPT ChainReduction ChainLowRankMN

variable {n m k : ℕ}

/-! ## Part 1. Schmidt-number bookkeeping -/

theorem isSchmidtLE_of_fintype {ι : Type*} [Fintype ι] (α : ι → Fin k → Fin n → ℂ)
    (β : ι → Fin k → Fin m → ℂ) :
    IsSchmidtLE k (∑ i, vecMulVec (schmidtVec (α i) (β i)) (star (schmidtVec (α i) (β i)))) := by
  classical
  let e := (Fintype.equivFin ι).symm
  exact ⟨Fintype.card ι, fun s => α (e s), fun s => β (e s),
    (Equiv.sum_comp e (fun i => vecMulVec (schmidtVec (α i) (β i)) (star (schmidtVec (α i) (β i))))).symm⟩

theorem IsSchmidtLE.add {ρ σ : Mat n m} (h₁ : IsSchmidtLE k ρ) (h₂ : IsSchmidtLE k σ) :
    IsSchmidtLE k (ρ + σ) := by
  obtain ⟨t₁, α₁, β₁, rfl⟩ := h₁
  obtain ⟨t₂, α₂, β₂, rfl⟩ := h₂
  refine ⟨t₁ + t₂, Fin.append α₁ α₂, Fin.append β₁ β₂, ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-! ## Part 2. Blocks along `ℂ³ = ℂ² ⊕ ℂ` -/

/-- The top block: the compression of the reference `ℂ³` to its first two coordinates. -/
def topBlock (ρ : Mat 3 n) : Mat 2 n := fun x y => ρ (x.1.castSucc, x.2) (y.1.castSucc, y.2)

/-- The cross block, between the first two reference coordinates and the last. -/
def crossBlock (ρ : Mat 3 n) : Matrix (Idx 2 n) (Fin n) ℂ := fun x l => ρ (x.1.castSucc, x.2) (Fin.last 2, l)

/-- The bottom block, at the last reference coordinate. -/
def botBlock (ρ : Mat 3 n) : Matrix (Fin n) (Fin n) ℂ := fun k l => ρ (Fin.last 2, k) (Fin.last 2, l)

/-- The vector `a ⊕ b` on `(ℂ² ⊕ ℂ) ⊗ ℂⁿ`. -/
def joinVec (a : Idx 2 n → ℂ) (b : Fin n → ℂ) : Idx 3 n → ℂ :=
  fun z => Fin.lastCases (b z.2) (fun i => a (i, z.2)) z.1

@[simp] theorem joinVec_castSucc (a : Idx 2 n → ℂ) (b : Fin n → ℂ) (i : Fin 2) (k : Fin n) :
    joinVec a b (i.castSucc, k) = a (i, k) := by
  simp only [joinVec, Fin.lastCases_castSucc]

@[simp] theorem joinVec_last (a : Idx 2 n → ℂ) (b : Fin n → ℂ) (k : Fin n) :
    joinVec a b (Fin.last 2, k) = b k := by
  simp only [joinVec, Fin.lastCases_last]

theorem sum_idx_three (f : Idx 3 n → ℂ) :
    ∑ z, f z = ∑ x : Idx 2 n, f (x.1.castSucc, x.2) + ∑ l, f (Fin.last 2, l) := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc, Fintype.sum_prod_type]

theorem mulVec_joinVec_top (ρ : Mat 3 n) (a : Idx 2 n → ℂ) (b : Fin n → ℂ) (x : Idx 2 n) :
    (ρ *ᵥ joinVec a b) (x.1.castSucc, x.2) = (topBlock ρ *ᵥ a) x + (crossBlock ρ *ᵥ b) x := by
  simp only [mulVec, dotProduct, sum_idx_three, joinVec_castSucc, joinVec_last, topBlock, crossBlock]

theorem mulVec_joinVec_last {ρ : Mat 3 n} (hH : ρᴴ = ρ) (a : Idx 2 n → ℂ) (b : Fin n → ℂ) (l : Fin n) :
    (ρ *ᵥ joinVec a b) (Fin.last 2, l) = ((crossBlock ρ)ᴴ *ᵥ a) l + (botBlock ρ *ᵥ b) l := by
  have e : ∀ y : Idx 2 n, ρ (Fin.last 2, l) (y.1.castSucc, y.2) = star (ρ (y.1.castSucc, y.2) (Fin.last 2, l)) :=
    fun y => by rw [← conjTranspose_apply, hH]
  simp only [mulVec, dotProduct, sum_idx_three, joinVec_castSucc, joinVec_last, botBlock, crossBlock,
    conjTranspose_apply, e]

theorem quad_joinVec {ρ : Mat 3 n} (hH : ρᴴ = ρ) (a : Idx 2 n → ℂ) (b : Fin n → ℂ) :
    star (joinVec a b) ⬝ᵥ (ρ *ᵥ joinVec a b) =
      star a ⬝ᵥ (topBlock ρ *ᵥ a) + star a ⬝ᵥ (crossBlock ρ *ᵥ b) +
        (star b ⬝ᵥ ((crossBlock ρ)ᴴ *ᵥ a) + star b ⬝ᵥ (botBlock ρ *ᵥ b)) := by
  rw [dotProduct, sum_idx_three]
  simp only [Pi.star_apply, joinVec_castSucc, joinVec_last, mulVec_joinVec_top, mulVec_joinVec_last hH, mul_add,
    Finset.sum_add_distrib, dotProduct, Prod.mk.eta]

theorem isPSD_topBlock {ρ : Mat 3 n} (h : IsPSD ρ) : IsPSD (topBlock ρ) := fun a => by
  have e := quad_joinVec h.hermitian a 0
  simp only [mulVec_zero, dotProduct_zero, star_zero, zero_dotProduct, add_zero] at e
  rw [← e]
  exact h _

theorem pt_topBlock (ρ : Mat 3 n) : pt (topBlock ρ) = topBlock (pt ρ) := rfl

theorem isPPT_topBlock {ρ : Mat 3 n} (h : IsPPT ρ) : IsPPT (topBlock ρ) :=
  ⟨isPSD_topBlock h.1, by rw [pt_topBlock]; exact isPSD_topBlock h.2⟩

/-! ## Part 3. The lifting lemma -/

theorem star_mulVec_dotProduct_mulVec {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] (A : Matrix ι κ ℂ)
    (B : Matrix ι μ ℂ) (u : κ → ℂ) (v : μ → ℂ) : star (A *ᵥ u) ⬝ᵥ (B *ᵥ v) = star u ⬝ᵥ ((Aᴴ * B) *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem vecMulVec_star_mulVec {ι κ μ : Type*} [Fintype μ] (u : ι → ℂ) (M : Matrix κ μ ℂ) (v : μ → ℂ) :
    vecMulVec u (star (M *ᵥ v)) = vecMulVec u (star v) * Mᴴ := by
  ext i j
  simp only [vecMulVec_apply, mulVec, dotProduct, Pi.star_apply, star_sum, star_mul', Matrix.mul_apply,
    conjTranspose_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The two-term vector `x ⊗ y + e₂ ⊗ g` as a sum of two product vectors. -/
theorem joinVec_prodVec (x : Fin 2 → ℂ) (y g : Fin n → ℂ) :
    joinVec (prodVec x y) g =
      schmidtVec ![fun a => Fin.lastCases 0 x a, Pi.single (Fin.last 2) 1] ![y, g] := by
  ext ⟨a, l⟩
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [joinVec_last, schmidtVec, Finset.sum_apply, Fin.sum_univ_two, prodVec, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.lastCases_last, Pi.single_eq_same, zero_mul, one_mul, zero_add]
  · simp only [joinVec_castSucc, schmidtVec, Finset.sum_apply, Fin.sum_univ_two, prodVec, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.lastCases_castSucc, Pi.single_eq_of_ne (Fin.castSucc_ne_last i), zero_mul,
      add_zero]

theorem joinVec_zero (r : Fin n → ℂ) :
    joinVec 0 r = schmidtVec ![Pi.single (Fin.last 2) 1, 0] ![r, 0] := by
  ext ⟨a, l⟩
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [joinVec_last, schmidtVec, Finset.sum_apply, Fin.sum_univ_two, prodVec, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.single_eq_same, one_mul, Pi.zero_apply, zero_mul, add_zero]
  · simp only [joinVec_castSucc, schmidtVec, Finset.sum_apply, Fin.sum_univ_two, prodVec, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.single_eq_of_ne (Fin.castSucc_ne_last i), Pi.zero_apply, zero_mul, add_zero]

/-- **The lifting lemma**: if the top block of a positive operator on `ℂ³ ⊗ ℂⁿ` is separable, the operator
has Schmidt number at most 2. With `D`, `K`, `T` the top, cross and bottom blocks and `D⁺` the
pseudo-inverse of `D`, write `D = Σ_s f_s f_s†` with product vectors `f_s`; then
`ρ = Σ_s (f_s ⊕ Kᴴ D⁺ f_s)(f_s ⊕ Kᴴ D⁺ f_s)† + (0 ⊕ (T - Kᴴ D⁺ K))`, every vector of which is a sum of two
product vectors. -/
theorem isSchmidtLE_two_of_topBlock {ρ : Mat 3 n} (hρ : IsPSD ρ) (hD : IsSeparable (topBlock ρ)) :
    IsSchmidtLE 2 ρ := by
  have hH : ρᴴ = ρ := hρ.hermitian
  set D := topBlock ρ with hDdef
  set K := crossBlock ρ with hKdef
  set T := botBlock ρ with hTdef
  have hDpsd : IsPSD D := isPSD_topBlock hρ
  have hDH : Dᴴ = D := hDpsd.hermitian
  obtain ⟨W, hWW, hker, hdet⟩ := exists_support hDpsd
  obtain ⟨M, hM⟩ : ∃ M, M = Wᴴ * D * W := ⟨_, rfl⟩
  have hMu : IsUnit M.det := by rw [hM]; exact isUnit_iff_ne_zero.2 hdet
  obtain ⟨Dp, hDp⟩ : ∃ Dp : Matrix (Idx 2 n) (Idx 2 n) ℂ, Dp = W * M⁻¹ * Wᴴ := ⟨_, rfl⟩
  set P : Matrix (Idx 2 n) (Idx 2 n) ℂ := 1 - W * Wᴴ with hP
  -- The pseudo-inverse.
  have h1 : D * (W * Wᴴ) = D := by
    have := hker
    rw [hP, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have h2 : W * Wᴴ * D = D := by
    have := congrArg conjTranspose h1
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hDH] at this
  have hDW : D * W = W * M := by
    calc D * W = W * Wᴴ * D * W := by rw [h2]
      _ = W * M := by rw [hM]; simp only [Matrix.mul_assoc]
  have hWD : Wᴴ * D = M * Wᴴ := by
    calc Wᴴ * D = Wᴴ * (D * (W * Wᴴ)) := by rw [h1]
      _ = M * Wᴴ := by rw [hM]; simp only [Matrix.mul_assoc]
  have hMH : Mᴴ = M := by
    rw [hM, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hDH, Matrix.mul_assoc]
  have hDpH : Dpᴴ = Dp := by
    rw [hDp, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hMH,
      Matrix.mul_assoc]
  have hDDp : D * Dp = W * Wᴴ := by
    rw [hDp, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hDW, Matrix.mul_assoc W M, mul_nonsing_inv _ hMu,
      Matrix.mul_one]
  have hDpD : Dp * D = W * Wᴴ := by
    rw [hDp, Matrix.mul_assoc, hWD, ← Matrix.mul_assoc, Matrix.mul_assoc W, nonsing_inv_mul _ hMu, Matrix.mul_one]
  have hDpDDp : Dp * D * Dp = Dp := by
    rw [hDpD, hDp, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc W, hWW, Matrix.mul_one]
  -- The cross block lives on the support of `D`.
  have hcol : ∀ c : Idx 2 n, Kᴴ *ᵥ (fun x => P x c) = 0 := fun c => by
    have hDv : D *ᵥ (fun x => P x c) = 0 := by
      ext x
      have := congrFun (congrFun hker x) c
      simpa [Matrix.mul_apply, mulVec, dotProduct] using this
    have hq : star (joinVec (fun x => P x c) 0) ⬝ᵥ (ρ *ᵥ joinVec (fun x => P x c) 0) = 0 := by
      rw [quad_joinVec hH, ← hDdef, hDv]
      simp
    have h0 := isPSD_mulVec_eq_zero hρ hq
    ext l
    have := congrFun h0 (Fin.last 2, l)
    rw [mulVec_joinVec_last hH] at this
    simpa using this
  have hKP : Kᴴ * P = 0 := by
    ext l c
    have := congrFun (hcol c) l
    simpa [Matrix.mul_apply, mulVec, dotProduct] using this
  have hWK : W * Wᴴ * K = K := by
    have hPH : Pᴴ = P := by
      rw [hP, conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]
    have := congrArg conjTranspose hKP
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hPH, conjTranspose_zero, hP, Matrix.sub_mul, Matrix.one_mul,
      sub_eq_zero] at this
    exact this.symm
  -- The generalized Schur complement.
  have hA : (Dp * K)ᴴ * D * (Dp * K) = Kᴴ * Dp * K := by
    rw [conjTranspose_mul, hDpH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc D, ← Matrix.mul_assoc Dp, ← Matrix.mul_assoc Dp D Dp, hDpDDp]
  have hB : (Dp * K)ᴴ * K = Kᴴ * Dp * K := by rw [conjTranspose_mul, hDpH]
  have hR : IsPSD (T - Kᴴ * Dp * K) := fun w => by
    have e := quad_joinVec hH (-((Dp * K) *ᵥ w)) w
    have e1 : star (-((Dp * K) *ᵥ w)) ⬝ᵥ (D *ᵥ -((Dp * K) *ᵥ w)) = star w ⬝ᵥ ((Kᴴ * Dp * K) *ᵥ w) := by
      rw [mulVec_neg, star_neg, neg_dotProduct, dotProduct_neg, neg_neg, mulVec_mulVec,
        star_mulVec_dotProduct_mulVec, ← Matrix.mul_assoc, hA]
    have e2 : star (-((Dp * K) *ᵥ w)) ⬝ᵥ (K *ᵥ w) = -(star w ⬝ᵥ ((Kᴴ * Dp * K) *ᵥ w)) := by
      rw [star_neg, neg_dotProduct, star_mulVec_dotProduct_mulVec, hB]
    have e3 : star w ⬝ᵥ (Kᴴ *ᵥ -((Dp * K) *ᵥ w)) = -(star w ⬝ᵥ ((Kᴴ * Dp * K) *ᵥ w)) := by
      rw [mulVec_neg, dotProduct_neg, mulVec_mulVec, ← Matrix.mul_assoc]
    rw [← hDdef, ← hKdef, ← hTdef, e1, e2, e3] at e
    have e4 : star w ⬝ᵥ ((T - Kᴴ * Dp * K) *ᵥ w) = star (joinVec (-((Dp * K) *ᵥ w)) w) ⬝ᵥ
        (ρ *ᵥ joinVec (-((Dp * K) *ᵥ w)) w) := by
      rw [e, sub_mulVec, dotProduct_sub]
      ring
    rw [e4]
    exact hρ _
  -- The decomposition.
  obtain ⟨t, x, y, hxy⟩ := hD
  obtain ⟨B, hB⟩ := hR.gram
  set f : Fin t → Idx 2 n → ℂ := fun s => prodVec (x s) (y s) with hf
  set g : Fin t → Fin n → ℂ := fun s => (Kᴴ * Dp) *ᵥ f s with hg
  have hFF : ∑ s, vecMulVec (f s) (star (f s)) = D := hxy.symm
  have hFG : ∑ s, vecMulVec (f s) (star (g s)) = K := by
    have e : ∑ s, vecMulVec (f s) (star (g s)) = (∑ s, vecMulVec (f s) (star (f s))) * (Kᴴ * Dp)ᴴ := by
      rw [Matrix.sum_mul]
      exact Finset.sum_congr rfl fun s _ => vecMulVec_star_mulVec _ _ _
    rw [e, hFF, conjTranspose_mul, conjTranspose_conjTranspose, hDpH, ← Matrix.mul_assoc, hDDp, hWK]
  have hGG : ∑ s, vecMulVec (g s) (star (g s)) = Kᴴ * Dp * K := by
    have e : ∑ s, vecMulVec (g s) (star (g s)) =
        Kᴴ * Dp * (∑ s, vecMulVec (f s) (star (f s))) * (Kᴴ * Dp)ᴴ := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      exact Finset.sum_congr rfl fun s _ => MathLab.vecMulVec_mulVec_star _ _
    rw [e, hFF, conjTranspose_mul, conjTranspose_conjTranspose, hDpH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc D, ← Matrix.mul_assoc Dp, ← Matrix.mul_assoc Dp D Dp, hDpDDp]
  have hRR : ∑ j, vecMulVec (star (B j)) (star (star (B j))) = T - Kᴴ * Dp * K := by
    rw [hB, conjTranspose_mul_self_eq_sum']
    simp only [star_star]
  have hmain : ρ = ∑ s, vecMulVec (joinVec (f s) (g s)) (star (joinVec (f s) (g s))) +
      ∑ j, vecMulVec (joinVec 0 (star (B j))) (star (joinVec 0 (star (B j)))) := by
    ext ⟨a, k⟩ ⟨b, l⟩
    refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b
    · have eG := congrFun (congrFun hGG k) l
      have eR := congrFun (congrFun hRR k) l
      simp only [Matrix.sum_apply, vecMulVec_apply, Pi.star_apply] at eG eR
      simp only [Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply, joinVec_last, eG, eR,
        Matrix.sub_apply, hTdef, botBlock]
      ring
    · have eG := congrFun (congrFun hFG (b', l)) k
      simp only [Matrix.sum_apply, vecMulVec_apply, Pi.star_apply] at eG
      have e : ρ (Fin.last 2, k) (b'.castSucc, l) = star (K (b', l) k) := by
        show _ = star (ρ (b'.castSucc, l) (Fin.last 2, k))
        rw [← conjTranspose_apply, hH]
      simp only [Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply, joinVec_last,
        joinVec_castSucc, Pi.zero_apply, star_zero, mul_zero, Finset.sum_const_zero, add_zero]
      rw [e, ← eG, star_sum]
      exact Finset.sum_congr rfl fun _ _ => by rw [star_mul', star_star, mul_comm]
    · have eG := congrFun (congrFun hFG (a', k)) l
      simp only [Matrix.sum_apply, vecMulVec_apply, Pi.star_apply] at eG
      simp only [Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply, joinVec_last,
        joinVec_castSucc, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, eG, hKdef, crossBlock]
    · have eF := congrFun (congrFun hFF (a', k)) (b', l)
      simp only [Matrix.sum_apply, vecMulVec_apply, Pi.star_apply] at eF
      simp only [Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply, joinVec_castSucc,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, eF, hDdef, topBlock]
  rw [hmain]
  simp only [hf, joinVec_prodVec, joinVec_zero]
  exact (isSchmidtLE_of_fintype _ _).add (isSchmidtLE_of_fintype _ _)

/-! ## Part 4. Qutrits -/

/-- **Every PPT operator on `ℂ³ ⊗ ℂ³` has Schmidt number at most 2** (Yang, Leung and Tang 2016, in its dual
form): its top block is PPT on `ℂ² ⊗ ℂ³`, hence separable by Woronowicz's theorem. -/
theorem isSchmidtLE_two_of_isPPT {ρ : Mat 3 3} (h : IsPPT ρ) : IsSchmidtLE 2 ρ :=
  isSchmidtLE_two_of_topBlock h.1 (pptSeparable23 _ (isPPT_topBlock h))

/-- **PPT² on `M_3`** (Christandl, Müller-Hermes and Wolf 2019; Chen, Yang and Tang 2019): the composition of
two PPT maps on `M_3` is entanglement breaking. -/
theorem pptSquared_three : PPTSquared 3 :=
  pptSquared_three_of_schmidt fun _ h => isSchmidtLE_two_of_isPPT h

end Channels

end

end -- public section

#print axioms Channels.isSchmidtLE_two_of_topBlock
#print axioms Channels.isSchmidtLE_two_of_isPPT
#print axioms Channels.pptSquared_three

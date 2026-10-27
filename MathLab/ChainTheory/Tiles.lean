module

/-
Tiles.lean

**A PPT entangled state of rank four**, from the "tiles" unextendible product basis of Bennett,
DiVincenzo, Mor, Shor, Smolin and Terhal (Phys. Rev. Lett. 82 (1999) 5385). The five product vectors
ψⱼ = aⱼ ⊗ bⱼ on ℂ³ ⊗ ℂ³ below are orthogonal, and no nonzero product vector is orthogonal to all of them.
The normalized projector onto their orthogonal complement, ρ = (1 - Σⱼ ψⱼψⱼ†/‖ψⱼ‖²)/4, has rational
entries and rank four. It equals its partial transpose (every ψⱼ is real), so it is PPT, and it is
entangled by the range criterion.

  Part 1  The range criterion (P. Horodecki 1997), kernel form: a nonzero separable operator has a
          nonzero product vector orthogonal to its kernel.
  Part 2  The tiles basis is unextendible.
  Part 3  The tiles state: PPT, rank four, not separable.
-/
public import MathLab.ChainTheory.Reduction

@[expose] public section

open Matrix ComplexOrder Module

noncomputable section

namespace ChainTiles

open ChoiDark ChainDuality ChainPPT ChainReduction

variable {n m : ℕ}

/-! ## Part 1. The range criterion -/

/-- **The range criterion** (P. Horodecki 1997), kernel form: a nonzero separable operator has a nonzero
product vector orthogonal to its kernel. Each product vector of a separable decomposition is. -/
theorem exists_prodVec_of_isSeparable {ρ : Mat n m} (h : IsSeparable ρ) (h0 : ρ ≠ 0) :
    ∃ x y, prodVec x y ≠ 0 ∧ ∀ v, ρ *ᵥ v = 0 → star (prodVec x y) ⬝ᵥ v = 0 := by
  obtain ⟨r, x, y, rfl⟩ := h
  obtain ⟨s, hs⟩ : ∃ s, prodVec (x s) (y s) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h0 (by simp [hall])
  refine ⟨x s, y s, hs, fun v hv => ?_⟩
  have hq : star v ⬝ᵥ ((∑ t, vecMulVec (prodVec (x t) (y t)) (star (prodVec (x t) (y t)))) *ᵥ v) = 0 := by
    rw [hv, dotProduct_zero]
  rw [Matrix.sum_mulVec, dotProduct_sum] at hq
  simp only [quad_rank_one] at hq
  have hre : ∑ t, Complex.normSq (star (prodVec (x t) (y t)) ⬝ᵥ v) = 0 := by
    have h1 := congrArg Complex.re hq
    rwa [Complex.re_sum, Complex.zero_re] at h1
  exact Complex.normSq_eq_zero.1
    ((Finset.sum_eq_zero_iff_of_nonneg fun t _ => Complex.normSq_nonneg _).1 hre s (Finset.mem_univ s))

/-! ## Part 2. The tiles basis is unextendible -/

/-- The first-factor parts `aⱼ` of the five tiles. -/
def tilesA : Fin 5 → Fin 3 → ℚ := ![![1, 0, 0], ![0, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, 1]]

/-- The second-factor parts `bⱼ` of the five tiles. -/
def tilesB : Fin 5 → Fin 3 → ℚ := ![![1, -1, 0], ![0, 1, -1], ![0, 0, 1], ![1, 0, 0], ![1, 1, 1]]

theorem eq_zero_of_three {x : Fin 3 → ℂ} (h0 : x 0 = 0) (h1 : x 1 = 0) (h2 : x 2 = 0) : x = 0 := by
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **The tiles basis is unextendible**: if `x ⊗ y` is orthogonal to the five tiles, then `x = 0` or
`y = 0`. Any three of the `aⱼ`, and any three of the `bⱼ`, span ℂ³. -/
theorem tiles_unextendible (x y : Fin 3 → ℂ)
    (h : ∀ j, (∑ a, (tilesA j a : ℂ) * x a) * (∑ k, (tilesB j k : ℂ) * y k) = 0) : x = 0 ∨ y = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  simp [tilesA, tilesB, Fin.sum_univ_three] at h0 h1 h2 h3 h4
  rcases h0 with h0 | h0
  · rcases h2 with h2 | h2
    · have hx1 : x 1 = 0 := by linear_combination h0 - h2
      rcases h3 with h3 | h3
      · exact Or.inl (eq_zero_of_three h0 hx1 (by linear_combination hx1 - h3))
      · rcases h1 with h1 | h1
        · exact Or.inl (eq_zero_of_three h0 hx1 h1)
        · rcases h4 with h4 | h4
          · exact Or.inl (eq_zero_of_three h0 hx1 (by linear_combination h4 - h0 - hx1))
          · have hy1 : y 1 = 0 := by linear_combination (h4 - h3 + h1) / 2
            exact Or.inr (eq_zero_of_three h3 hy1 (by linear_combination hy1 - h1))
    · rcases h1 with h1 | h1
      · rcases h3 with h3 | h3
        · exact Or.inl (eq_zero_of_three h0 (by linear_combination h3 + h1) h1)
        · rcases h4 with h4 | h4
          · exact Or.inl (eq_zero_of_three h0 (by linear_combination h4 - h0 - h1) h1)
          · exact Or.inr (eq_zero_of_three h3 (by linear_combination h4 - h3 - h2) h2)
      · have hy1 : y 1 = 0 := by linear_combination h1 + h2
        rcases h3 with h3 | h3
        · rcases h4 with h4 | h4
          · have hx1 : x 1 = 0 := by linear_combination (h4 - h0 + h3) / 2
            exact Or.inl (eq_zero_of_three h0 hx1 (by linear_combination hx1 - h3))
          · exact Or.inr (eq_zero_of_three (by linear_combination h4 - hy1 - h2) hy1 h2)
        · exact Or.inr (eq_zero_of_three h3 hy1 h2)
  · rcases h1 with h1 | h1
    · rcases h3 with h3 | h3
      · have hx1 : x 1 = 0 := by linear_combination h3 + h1
        rcases h2 with h2 | h2
        · exact Or.inl (eq_zero_of_three (by linear_combination h2 + hx1) hx1 h1)
        · rcases h4 with h4 | h4
          · exact Or.inl (eq_zero_of_three (by linear_combination h4 - hx1 - h1) hx1 h1)
          · have hy0 : y 0 = 0 := by linear_combination (h4 + h0 - h2) / 2
            exact Or.inr (eq_zero_of_three hy0 (by linear_combination hy0 - h0) h2)
      · have hy1 : y 1 = 0 := by linear_combination h3 - h0
        rcases h2 with h2 | h2
        · rcases h4 with h4 | h4
          · have hx0 : x 0 = 0 := by linear_combination (h4 - h1 + h2) / 2
            exact Or.inl (eq_zero_of_three hx0 (by linear_combination hx0 - h2) h1)
          · exact Or.inr (eq_zero_of_three h3 hy1 (by linear_combination h4 - h3 - hy1))
        · exact Or.inr (eq_zero_of_three h3 hy1 h2)
    · rcases h3 with h3 | h3
      · rcases h2 with h2 | h2
        · rcases h4 with h4 | h4
          · have hx0 : x 0 = 0 := by linear_combination (h4 + 2 * h2 + h3) / 3
            have hx1 : x 1 = 0 := by linear_combination hx0 - h2
            exact Or.inl (eq_zero_of_three hx0 hx1 (by linear_combination hx1 - h3))
          · have hy0 : y 0 = 0 := by linear_combination (h4 + 2 * h0 + h1) / 3
            have hy1 : y 1 = 0 := by linear_combination hy0 - h0
            exact Or.inr (eq_zero_of_three hy0 hy1 (by linear_combination hy1 - h1))
        · have hy1 : y 1 = 0 := by linear_combination h1 + h2
          exact Or.inr (eq_zero_of_three (by linear_combination h0 + hy1) hy1 h2)
      · have hy1 : y 1 = 0 := by linear_combination h3 - h0
        exact Or.inr (eq_zero_of_three h3 hy1 (by linear_combination hy1 - h1))

/-! ## Part 3. The tiles state -/

/-- The squared norms `‖ψⱼ‖²` of the five tiles. -/
def tilesNorm : Fin 5 → ℚ := ![2, 2, 2, 2, 9]

/-- The tiles state `(1 - Σⱼ ψⱼψⱼ†/‖ψⱼ‖²)/4` as a rational table. -/
def tilesQ (x y : Fin 3 × Fin 3) : ℚ :=
  ((if x = y then 1 else 0) - ∑ j, tilesA j x.1 * tilesB j x.2 * tilesA j y.1 * tilesB j y.2 / tilesNorm j) / 4

/-- The index `3a + k` of `(a, k)`. -/
def ix3 (a k : Fin 3) : Fin 9 := ⟨3 * a.val + k.val, by omega⟩

/-- Four orthogonal vectors spanning the complement of the tiles. -/
def tilesVec9 : Fin 4 → Fin 9 → ℚ :=
  ![![7, 7, -2, -2, -2, -2, -2, -2, -2], ![0, 0, 5, -2, -2, 5, -2, -2, -2], ![0, 0, 0, 3, -2, 0, 3, -2, -2],
    ![0, 0, 0, 0, 2, 0, 0, -1, -1]]

def tilesVec (j : Fin 4) (x : Fin 3 × Fin 3) : ℚ := tilesVec9 j (ix3 x.1 x.2)

/-- The weights `1/(4 ‖vⱼ‖²)`. -/
def tilesWt : Fin 4 → ℚ := ![1 / 504, 1 / 280, 1 / 120, 1 / 24]

theorem tilesQ_eq : ∀ x y, tilesQ x y = ∑ j, tilesWt j * tilesVec j x * tilesVec j y := by
  decide +kernel

theorem tilesQ_pt : ∀ a k b l : Fin 3, tilesQ (a, l) (b, k) = tilesQ (a, k) (b, l) := by
  decide +kernel

theorem tilesQ_kernel : ∀ (j : Fin 5) (x : Fin 3 × Fin 3),
    ∑ y : Fin 3 × Fin 3, tilesQ x y * (tilesA j y.1 * tilesB j y.2) = 0 := by
  decide +kernel

theorem tilesQ_trace : ∑ x : Fin 3 × Fin 3, tilesQ x x = 1 := by
  decide +kernel

/-- The principal block on `(0,0), (0,2), (1,0), (1,1)` and its inverse. -/
def tilesSub : Fin 4 → Fin 3 × Fin 3 := ![(0, 0), (0, 2), (1, 0), (1, 1)]

def tilesSubInv : Fin 4 → Fin 4 → ℚ := ![![16, 8, 8, 4], ![8, 16, 8, 4], ![8, 8, 16, 4], ![4, 4, 4, 6]]

theorem tilesQ_sub_inv : ∀ i j : Fin 4,
    ∑ l, tilesQ (tilesSub i) (tilesSub l) * tilesSubInv l j = if i = j then 1 else 0 := by
  decide +kernel

/-- The tiles state on `ℂ³ ⊗ ℂ³`. -/
def tiles : Mat 3 3 := fun x y => (tilesQ x y : ℂ)

theorem isPSD_tiles : IsPSD tiles :=
  isPSD_of_rat_sum tilesWt (by decide +kernel) tilesVec fun s t => by
    simp only [tiles, tilesQ_eq]
    push_cast
    rfl

/-- The tiles state equals its partial transpose. -/
theorem pt_tiles : pt tiles = tiles := by
  ext x y
  simp only [pt, tiles]
  exact_mod_cast tilesQ_pt x.1 x.2 y.1 y.2

theorem isPPT_tiles : IsPPT tiles := ⟨isPSD_tiles, by rw [pt_tiles]; exact isPSD_tiles⟩

theorem tiles_ne_zero : tiles ≠ 0 := by
  intro h
  have h1 : ∑ x, tiles x x = 1 := by
    simp only [tiles]
    exact_mod_cast tilesQ_trace
  rw [h] at h1
  simp at h1

/-- The tile `ψⱼ` as a vector. -/
def tile (j : Fin 5) : Fin 3 × Fin 3 → ℂ := fun y => ((tilesA j y.1 * tilesB j y.2 : ℚ) : ℂ)

theorem tiles_mulVec_tile (j : Fin 5) : tiles *ᵥ tile j = 0 := by
  funext x
  have h := congrArg (fun q : ℚ => (q : ℂ)) (tilesQ_kernel j x)
  push_cast at h
  simpa [mulVec, dotProduct, tiles, tile] using h

/-- **The tiles state is not separable**: by the range criterion, a separable decomposition would contain
a nonzero product vector orthogonal to the five tiles. -/
theorem not_isSeparable_tiles : ¬ IsSeparable tiles := by
  intro hs
  obtain ⟨x, y, hxy, horth⟩ := exists_prodVec_of_isSeparable hs tiles_ne_zero
  have key : ∀ j, (∑ a, (tilesA j a : ℂ) * star (x a)) * (∑ k, (tilesB j k : ℂ) * star (y k)) = 0 := by
    intro j
    have h := horth (tile j) (tiles_mulVec_tile j)
    rw [Finset.sum_mul_sum, ← h]
    simp only [dotProduct, prodVec, tile, Pi.star_apply, star_mul', Fintype.sum_prod_type]
    push_cast
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rcases tiles_unextendible (fun a => star (x a)) (fun k => star (y k)) key with h | h
  · apply hxy
    funext z
    have hz := congrFun h z.1
    simp only [Pi.zero_apply, star_eq_zero] at hz
    simp [prodVec, hz]
  · apply hxy
    funext z
    have hz := congrFun h z.2
    simp only [Pi.zero_apply, star_eq_zero] at hz
    simp [prodVec, hz]

/-- **The tiles state has rank four**: four rank-one terms, and an invertible 4 × 4 principal block. -/
theorem rank_tiles : tiles.rank = 4 := by
  apply le_antisymm
  · set V : Matrix (Fin 3 × Fin 3) (Fin 4) ℂ := Matrix.of fun x j => (tilesVec j x : ℂ) with hV
    have e : tiles = V * diagonal (fun j => (tilesWt j : ℂ)) * Vᵀ := by
      ext x y
      rw [Matrix.mul_apply]
      simp only [mul_diagonal, transpose_apply, hV, Matrix.of_apply, tiles, tilesQ_eq]
      push_cast
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact (rank_mul_le_left _ _).trans ((rank_mul_le_left _ _).trans ((rank_le_card_width V).trans (by simp)))
  · have hinv : tiles.submatrix tilesSub tilesSub * Matrix.of (fun i j => (tilesSubInv i j : ℂ)) = 1 := by
      ext i j
      have h := congrArg (fun q : ℚ => (q : ℂ)) (tilesQ_sub_inv i j)
      push_cast at h
      rw [Matrix.mul_apply, Matrix.one_apply]
      simpa [tiles, apply_ite (fun q : ℚ => (q : ℂ))] using h
    have hdet : (tiles.submatrix tilesSub tilesSub).det ≠ 0 := (isUnit_det_of_right_inverse hinv).ne_zero
    have h4 := rank_of_det_ne_zero hdet
    rw [Fintype.card_fin] at h4
    rw [← h4]
    exact rank_submatrix_le _ _ _

/-- **A PPT entangled state of rank four** on `ℂ³ ⊗ ℂ³`. -/
theorem tiles_ppt_entangled : IsPPT tiles ∧ ¬ IsSeparable tiles ∧ tiles.rank = 4 :=
  ⟨isPPT_tiles, not_isSeparable_tiles, rank_tiles⟩

end ChainTiles

end

end -- public section

#print axioms ChainTiles.exists_prodVec_of_isSeparable
#print axioms ChainTiles.tiles_unextendible
#print axioms ChainTiles.tiles_ppt_entangled

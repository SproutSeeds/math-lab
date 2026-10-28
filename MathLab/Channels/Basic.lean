module

/-
Channels/Basic.lean

Linear maps between matrix algebras, as quantum channels, for the PPT² conjecture of M. Christandl.

  `IsCP Φ`        completely positive: the Choi matrix is positive semidefinite (Choi's theorem).
  `IsPPTMap Φ`    PPT: completely positive and completely copositive, i.e. the Choi matrix is PPT.
  `IsEB Φ`        entanglement breaking: the Choi matrix is separable (Horodecki, Shor and Ruskai).
  `PPTSquared d`  the conjecture on `M_d`: the composition of two PPT maps is entanglement breaking.

Each Choi condition is tied to its operational meaning for every ancilla: `applyR Φ` is `id ⊗ Φ` on an
operator on `ℂʳ ⊗ ℂⁿ` (`isCP_iff`, `isPPT_applyR`, `isEB_iff`). `PPTSquared d` is a `Prop`, not a
theorem. It holds for `d = 2` (`pptSquared_two`), and a single PPT map on `M_3` need not be entanglement
breaking (`exists_isPPTMap_not_isEB`), so the composition matters.
-/
public import MathLab.ChainTheory.LowRankMN

@[expose] public section

open Matrix
open scoped Kronecker

noncomputable section

namespace Channels

open ChoiDark ChainDuality ChainStormer ChainWoronowicz ChainPPT ChainReduction ChainLowRankMN

variable {n m p r : ℕ}

/-- Linear maps `M_n(ℂ) → M_m(ℂ)`. -/
abbrev Lin (n m : ℕ) := Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ

/-! ## Part 1. `id ⊗ Φ` and the Choi matrix -/

/-- `id ⊗ Φ` on an operator on `ℂʳ ⊗ ℂⁿ`: Φ acts on each block. -/
def applyR (Φ : Lin n m) (ρ : Mat r n) : Mat r m := fun x y => Φ (blkAt ρ x.1 y.1) x.2 y.2

/-- The unnormalized maximally entangled vector `Σ_a |a⟩|a⟩`. -/
def maxEntVec (n : ℕ) : Idx n n → ℂ := fun z => if z.1 = z.2 then 1 else 0

/-- Its projector. -/
def maxEnt (n : ℕ) : Mat n n := vecMulVec (maxEntVec n) (star (maxEntVec n))

theorem blkAt_maxEnt (a b : Fin n) : blkAt (maxEnt n) a b = single a b 1 := by
  ext k l
  simp only [blkAt, maxEnt, maxEntVec, vecMulVec_apply, Pi.star_apply, Matrix.single_apply]
  by_cases h1 : a = k <;> by_cases h2 : b = l <;> simp [h1, h2]

/-- **The Choi matrix is `id ⊗ Φ` of the maximally entangled projector.** -/
theorem applyR_maxEnt (Φ : Lin n m) : applyR Φ (maxEnt n) = choi Φ := by
  ext x y
  simp only [applyR, choi, blkAt_maxEnt]

/-- **A map is determined by its Choi matrix.** -/
theorem choiInv_choi (Φ : Lin n m) : choiInv (choi Φ) = Φ := by
  refine LinearMap.ext fun X => ?_
  conv_rhs => rw [matrix_eq_sum_single X]
  ext k l
  simp only [choiInv, choi, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show single a b (X a b) = X a b • single a b (1 : ℂ) by rw [smul_single, smul_eq_mul, mul_one],
    map_smul, Matrix.smul_apply, smul_eq_mul]

theorem applyR_sum {ι : Type*} (s : Finset ι) (Φ : Lin n m) (ρ : ι → Mat r n) :
    applyR Φ (∑ i ∈ s, ρ i) = ∑ i ∈ s, applyR Φ (ρ i) := by
  ext x y
  have e : blkAt (∑ i ∈ s, ρ i) x.1 y.1 = ∑ i ∈ s, blkAt (ρ i) x.1 y.1 := by
    ext k l
    simp [blkAt, Matrix.sum_apply]
  simp only [applyR, e, map_sum, Matrix.sum_apply]

/-- `id ⊗ Φ ∘ Ψ` is `(id ⊗ Φ) ∘ (id ⊗ Ψ)`. -/
theorem applyR_comp (Φ : Lin m p) (Ψ : Lin n m) (ρ : Mat r n) :
    applyR (Φ ∘ₗ Ψ) ρ = applyR Φ (applyR Ψ ρ) := rfl

/-- **The Choi matrix of a composition**: `C(Φ ∘ Ψ) = (id ⊗ Φ)(C(Ψ))`. -/
theorem choi_comp (Φ : Lin m p) (Ψ : Lin n m) : choi (Φ ∘ₗ Ψ) = applyR Φ (choi Ψ) := by
  rw [← applyR_maxEnt, applyR_comp, applyR_maxEnt]

/-- Operations on the first factor commute with `id ⊗ Φ`. -/
theorem blkAt_lop_left {r' : ℕ} (G : Matrix (Fin r') (Fin r) ℂ) (σ : Mat r n) (a b : Fin r') :
    blkAt (lop G (1 : Matrix (Fin n) (Fin n) ℂ) σ) a b = ∑ a', ∑ b', (G a a' * star (G b b')) • blkAt σ a' b' := by
  ext k l
  simp only [blkAt, lop_apply_one, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem applyR_lop_left {r' : ℕ} (Φ : Lin n m) (G : Matrix (Fin r') (Fin r) ℂ) (σ : Mat r n) :
    applyR Φ (lop G (1 : Matrix (Fin n) (Fin n) ℂ) σ) = lop G (1 : Matrix (Fin m) (Fin m) ℂ) (applyR Φ σ) := by
  ext ⟨a, k⟩ ⟨b, l⟩
  simp only [applyR, blkAt_lop_left, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    lop_apply_one]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-! ## Part 2. Complete positivity -/

/-- **Completely positive**, by Choi's theorem: the Choi matrix is positive semidefinite. -/
def IsCP (Φ : Lin n m) : Prop := IsPSD (choi Φ)

theorem isPSD_sum {ι κ : Type*} [Fintype κ] (s : Finset ι) {P : ι → Matrix κ κ ℂ}
    (h : ∀ i ∈ s, IsPSD (P i)) : IsPSD (∑ i ∈ s, P i) :=
  Finset.sum_induction _ IsPSD (fun _ _ => IsPSD.add) isPSD_zero h

/-- `Bᴴ B` as a sum of rank-one projectors. -/
theorem conjTranspose_mul_self_eq_sum' {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) :
    Bᴴ * B = ∑ s, vecMulVec (star (B s)) (B s) := by
  ext a b
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply]

/-- **Kraus form of a completely positive map.** -/
theorem exists_kraus {Φ : Lin n m} (h : IsCP Φ) :
    ∃ K : Idx n m → Matrix (Fin m) (Fin n) ℂ, ∀ X, Φ X = ∑ s, K s * X * (K s)ᴴ := by
  obtain ⟨B, hB⟩ := h.gram
  refine ⟨fun s => Matrix.of fun k a => star (B s (a, k)), fun X => ?_⟩
  conv_lhs => rw [← choiInv_choi Φ, hB]
  ext k l
  simp only [choiInv, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.mul_apply, conjTranspose_apply,
    Matrix.sum_apply, star_star, Finset.mul_sum, Finset.sum_mul]
  calc ∑ a, ∑ b, ∑ s, X a b * (star (B s (a, k)) * B s (b, l))
      = ∑ a, ∑ s, ∑ b, X a b * (star (B s (a, k)) * B s (b, l)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ s, ∑ a, ∑ b, X a b * (star (B s (a, k)) * B s (b, l)) := Finset.sum_comm
    _ = ∑ s, ∑ b, ∑ a, star (B s (a, k)) * X a b * B s (b, l) :=
        Finset.sum_congr rfl fun _ _ => by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- A map in Kraus form acts on the second factor as a sum of local operations. -/
theorem applyR_eq_sum_lop {Φ : Lin n m} {ι : Type*} [Fintype ι] {K : ι → Matrix (Fin m) (Fin n) ℂ}
    (hK : ∀ X, Φ X = ∑ s, K s * X * (K s)ᴴ) (ρ : Mat r n) :
    applyR Φ ρ = ∑ s, lop (1 : Matrix (Fin r) (Fin r) ℂ) (K s) ρ := by
  ext ⟨a, k⟩ ⟨b, l⟩
  simp only [applyR, hK, Matrix.sum_apply, lop_one_apply, Matrix.mul_apply, conjTranspose_apply, blkAt,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- **A completely positive map is positive on every ancilla.** -/
theorem isPSD_applyR {Φ : Lin n m} (h : IsCP Φ) {ρ : Mat r n} (hρ : IsPSD ρ) : IsPSD (applyR Φ ρ) := by
  obtain ⟨K, hK⟩ := exists_kraus h
  rw [applyR_eq_sum_lop hK]
  exact isPSD_sum _ fun s _ => isPSD_lop _ _ hρ

/-- **Complete positivity, operationally**: `id ⊗ Φ` is positive for every ancilla `ℂʳ`. -/
theorem isCP_iff (Φ : Lin n m) : IsCP Φ ↔ ∀ (r : ℕ) (ρ : Mat r n), IsPSD ρ → IsPSD (applyR Φ ρ) :=
  ⟨fun h _ _ hρ => isPSD_applyR h hρ, fun h => by
    have := h n (maxEnt n) (isPSD_rank_one _)
    rwa [applyR_maxEnt] at this⟩

/-! ## Part 3. PPT maps -/

/-- The transpose, as a linear map. -/
def transposeLin (m : ℕ) : Lin m m where
  toFun X := Xᵀ
  map_add' := transpose_add
  map_smul' c X := transpose_smul c X

theorem choi_transposeLin_comp (Φ : Lin n m) : choi (transposeLin m ∘ₗ Φ) = pt (choi Φ) := rfl

/-- **PPT map**: completely positive and completely copositive, i.e. its Choi matrix is PPT. -/
def IsPPTMap (Φ : Lin n m) : Prop := IsPPT (choi Φ)

theorem isPPTMap_iff (Φ : Lin n m) : IsPPTMap Φ ↔ IsCP Φ ∧ IsCP (transposeLin m ∘ₗ Φ) := by
  rw [IsCP, IsCP, choi_transposeLin_comp]
  rfl

theorem pt_applyR (Φ : Lin n m) (ρ : Mat r n) : pt (applyR Φ ρ) = applyR (transposeLin m ∘ₗ Φ) ρ := rfl

/-- **A PPT map sends every positive operator to a PPT one, on every ancilla.** -/
theorem isPPT_applyR {Φ : Lin n m} (h : IsPPTMap Φ) {ρ : Mat r n} (hρ : IsPSD ρ) : IsPPT (applyR Φ ρ) :=
  ⟨isPSD_applyR h.1 hρ, by
    rw [pt_applyR]
    exact isPSD_applyR (by rw [IsCP, choi_transposeLin_comp]; exact h.2) hρ⟩

/-! ## Part 4. Entanglement breaking maps -/

/-- **Entanglement breaking**: the Choi matrix is separable. -/
def IsEB (Φ : Lin n m) : Prop := IsSeparable (choi Φ)

/-- `Z ⊗ y y†` is separable for positive `Z`. -/
theorem isSeparable_kron_rank_one {Z : Matrix (Fin r) (Fin r) ℂ} (hZ : IsPSD Z) (y : Fin m → ℂ) :
    IsSeparable (Z ⊗ₖ vecMulVec y (star y)) := by
  obtain ⟨B, rfl⟩ := hZ.gram
  have e : (Bᴴ * B) ⊗ₖ vecMulVec y (star y) =
      ∑ s, vecMulVec (prodVec (star (B s)) y) (star (prodVec (star (B s)) y)) := by
    ext ⟨a, k⟩ ⟨b, l⟩
    simp only [kroneckerMap_apply, Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply, prodVec,
      Matrix.sum_apply, Pi.star_apply, star_mul', star_star, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  exact isSeparable_of_fintype _ _

/-- An entanglement breaking map acts on the second factor as `Σ_s Z_s ⊗ y_s y_s†`, with `Z_s` the
compression of the input by `x_s`. -/
theorem applyR_eq_sum_kron {Φ : Lin n m} {t : ℕ} {x : Fin t → Fin n → ℂ} {y : Fin t → Fin m → ℂ}
    (hΦ : choi Φ = ∑ s, vecMulVec (prodVec (x s) (y s)) (star (prodVec (x s) (y s)))) (ρ : Mat r n) :
    applyR Φ ρ = ∑ s, xBlock (swapM ρ) (x s) ⊗ₖ vecMulVec (y s) (star (y s)) := by
  ext ⟨a, k⟩ ⟨b, l⟩
  have e : applyR Φ ρ (a, k) (b, l) = choiInv (choi Φ) (blkAt ρ a b) k l := by rw [choiInv_choi]; rfl
  rw [e, hΦ]
  simp only [choiInv, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.sum_apply, vecMulVec_apply,
    prodVec, Pi.star_apply, star_mul', kroneckerMap_apply, xBlock, swapM, blkAt, Finset.mul_sum, Finset.sum_mul]
  calc ∑ a', ∑ b', ∑ s, ρ (a, a') (b, b') * (x s a' * y s k * (star (x s b') * star (y s l)))
      = ∑ a', ∑ s, ∑ b', ρ (a, a') (b, b') * (x s a' * y s k * (star (x s b') * star (y s l))) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ s, ∑ a', ∑ b', ρ (a, a') (b, b') * (x s a' * y s k * (star (x s b') * star (y s l))) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
        ring

/-- **An entanglement breaking map outputs separable operators, on every ancilla.** -/
theorem isSeparable_applyR {Φ : Lin n m} (h : IsEB Φ) {ρ : Mat r n} (hρ : IsPSD ρ) :
    IsSeparable (applyR Φ ρ) := by
  obtain ⟨t, x, y, hxy⟩ := h
  rw [applyR_eq_sum_kron hxy]
  exact isSeparable_sum _ _ fun s _ => isSeparable_kron_rank_one (isPSD_xBlock (isPSD_swapM hρ) _) _

/-- **Entanglement breaking, operationally**: `id ⊗ Φ` outputs separable operators for every ancilla. -/
theorem isEB_iff (Φ : Lin n m) : IsEB Φ ↔ ∀ (r : ℕ) (ρ : Mat r n), IsPSD ρ → IsSeparable (applyR Φ ρ) :=
  ⟨fun h _ _ hρ => isSeparable_applyR h hρ, fun h => by
    have := h n (maxEnt n) (isPSD_rank_one _)
    rwa [applyR_maxEnt] at this⟩

/-! ## Part 5. The PPT² conjecture -/

/-- **The PPT² conjecture on `M_d`** (M. Christandl): the composition of two PPT maps is entanglement
breaking. This is a `Prop`, not a theorem. -/
def PPTSquared (d : ℕ) : Prop := ∀ Φ Ψ : Lin d d, IsPPTMap Φ → IsPPTMap Ψ → IsEB (Φ ∘ₗ Ψ)

/-- **The Choi-state form**: PPT² on `M_d` says that a PPT map on the second factor sends every PPT
operator on `ℂᵈ ⊗ ℂᵈ` to a separable one. -/
theorem pptSquared_iff (d : ℕ) :
    PPTSquared d ↔ ∀ (Φ : Lin d d) (C : Mat d d), IsPPTMap Φ → IsPPT C → IsSeparable (applyR Φ C) := by
  constructor
  · intro h Φ C hΦ hC
    have := h Φ (choiInv C) hΦ (by rw [IsPPTMap, choi_choiInv]; exact hC)
    rwa [IsEB, choi_comp, choi_choiInv] at this
  · intro h Φ Ψ hΦ hΨ
    rw [IsEB, choi_comp]
    exact h Φ (choi Ψ) hΦ hΨ

/-- PPT² holds wherever PPT operators are separable. -/
theorem pptSquared_of_allPPTSeparable {d : ℕ} (hs : AllPPTSeparable d d) : PPTSquared d :=
  fun Φ Ψ hΦ hΨ => by
    rw [IsEB, choi_comp]
    exact hs _ (isPPT_applyR hΦ hΨ.1)

/-- **PPT² on `M_2`**, from the two-qubit theorem. -/
theorem pptSquared_two : PPTSquared 2 := pptSquared_of_allPPTSeparable pptSeparable22

/-- **One PPT map is not enough**: the map whose Choi matrix is the tiles state is PPT on `M_3` and not
entanglement breaking. -/
theorem exists_isPPTMap_not_isEB : ∃ Φ : Lin 3 3, IsPPTMap Φ ∧ ¬ IsEB Φ :=
  ⟨choiInv ChainTiles.tiles, by rw [IsPPTMap, choi_choiInv]; exact ChainTiles.tiles_ppt_entangled.1,
    by rw [IsEB, choi_choiInv]; exact ChainTiles.tiles_ppt_entangled.2.1⟩

end Channels

end

end -- public section

#print axioms Channels.choiInv_choi
#print axioms Channels.isCP_iff
#print axioms Channels.isPPT_applyR
#print axioms Channels.isEB_iff
#print axioms Channels.pptSquared_iff
#print axioms Channels.pptSquared_two
#print axioms Channels.exists_isPPTMap_not_isEB

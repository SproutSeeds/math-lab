module

/-
LowRankMN.lean

**PPT states of low rank are separable, in every dimension** (P. Horodecki, Lewenstein, Vidal and Cirac,
Phys. Rev. A 62 (2000) 032310): a PPT operator on ℂⁿ ⊗ ℂᵐ whose rank is at most that of a reduced
operator is separable. With rank-two separability and the tiles state, this gives the minimal rank of
PPT entanglement: every PPT state of rank at most three is separable, and the tiles state has rank four.

  Part 1  Compressions to rows, `X(r) = Σ_{a,b} r_a ρ_ab conj(r_b)`. A shear on two rows (`exists_shear_ker`)
          and induction over the rows give a row `r` with `r₀ = 1` and `ker X(r) ⊆ ker ρ_B`.
  Part 2  The normal form: when ρ_B is invertible, a local operation makes the `(0, 0)` block 1.
  Part 3  Rank m then forces the Gram form `ρ_ab = B_aᴴ B_b`.
  Part 4  PPT makes every combination `Σ c_b B_b` normal, so `B_aᴴ B_b = B_b B_aᴴ`.
  Part 5  Fuglede and simultaneous diagonalization give a product decomposition.
  Part 6  The theorem, after compressing ℂᵐ to the support of ρ_B, and its ρ_A form.
  Part 7  Rank three, and the minimal rank of PPT entanglement.
-/
public import MathLab.ChainTheory.Tiles
public import MathLab.Positivity.NormalFamily

@[expose] public section

open Matrix ComplexOrder Module
open scoped Kronecker

noncomputable section

namespace ChainLowRankMN

open ChoiDark ChainDuality ChainStormer ChainWoronowicz ChainPPT ChainReduction

variable {n m : ℕ}

/-! ## Part 1. Compressions to rows and the shear -/

/-- The compression `X(r) = Σ_{a,b} r_a ρ_ab conj(r_b)` of ρ to the row `r`. -/
def xBlock (ρ : Mat n m) (r : Fin n → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun k l => ∑ a, ∑ b, r a * ρ (a, k) (b, l) * star (r b)

/-- The cross term `Σ_{a,b} r_a ρ_ab conj(s_b)`. -/
def cross (ρ : Mat n m) (r s : Fin n → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun k l => ∑ a, ∑ b, r a * ρ (a, k) (b, l) * star (s b)

theorem quad_xBlock (ρ : Mat n m) (r : Fin n → ℂ) (w : Fin m → ℂ) :
    star w ⬝ᵥ (xBlock ρ r *ᵥ w) =
      star (prodVec (star r) w) ⬝ᵥ (ρ *ᵥ prodVec (star r) w) := by
  simp only [dotProduct, mulVec, xBlock, prodVec, Pi.star_apply, star_mul', star_star, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ k, ∑ a, ∑ l, ∑ b, star (w k) * (r a * ρ (a, k) (b, l) * star (r b) * w l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ k, ∑ l, ∑ b, star (w k) * (r a * ρ (a, k) (b, l) * star (r b) * w l) := Finset.sum_comm
    _ = ∑ a, ∑ k, ∑ b, ∑ l, star (w k) * (r a * ρ (a, k) (b, l) * star (r b) * w l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isPSD_xBlock {ρ : Mat n m} (h : IsPSD ρ) (r : Fin n → ℂ) : IsPSD (xBlock ρ r) := fun w => by
  rw [quad_xBlock]
  exact h _

theorem xBlock_single (ρ : Mat n m) (a : Fin n) :
    xBlock ρ (Pi.single a 1) = fun k l => ρ (a, k) (a, l) := by
  ext k l
  simp [xBlock, Pi.single_apply]

theorem redB_eq_sum_xBlock (ρ : Mat n m) : redB ρ = ∑ a, xBlock ρ (Pi.single a 1) := by
  ext k l
  simp [redB, xBlock, Matrix.sum_apply, Pi.single_apply]

/-- Two rows: the compression of ρ to the rows `r, s` is `[[X(r), cross], [crossᴴ, X(s)]]`. -/
theorem lop_rows_eq_blk {ρ : Mat n m} (hH : ρᴴ = ρ) (r s : Fin n → ℂ) :
    lop (Matrix.of ![r, s]) (1 : Matrix (Fin m) (Fin m) ℂ) ρ =
      blk (xBlock ρ r) (cross ρ r s) (cross ρ r s)ᴴ (xBlock ρ s) := by
  have hρ : ∀ x y, (starRingEnd ℂ) (ρ x y) = ρ y x := fun x y => by
    have := congrFun (congrFun hH y) x
    rwa [conjTranspose_apply] at this
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [lop_apply_one]
  fin_cases i <;> fin_cases j <;> simp [blk, xBlock, cross, conjTranspose_apply]
  simp only [hρ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem shear_rows (r s : Fin n → ℂ) (z : ℂ) :
    (!![(1 : ℂ), z; 0, 1] * Matrix.of ![r, s]) 0 = r + z • s := by
  funext b
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lop_apply_00 (G : Matrix (Fin 2) (Fin n) ℂ) (ρ : Mat n m) :
    blkOf (lop G (1 : Matrix (Fin m) (Fin m) ℂ) ρ) 0 0 = xBlock ρ (G 0) := by
  ext k l
  simp only [blkOf, lop_apply_one, xBlock]

theorem xBlock_add_smul {ρ : Mat n m} (hH : ρᴴ = ρ) (r s : Fin n → ℂ) (z : ℂ) :
    xBlock ρ (r + z • s) = xBlock ρ r + star z • cross ρ r s + z • (cross ρ r s)ᴴ +
      (z * star z) • xBlock ρ s := by
  have e : lop (!![(1 : ℂ), z; 0, 1] * Matrix.of ![r, s]) (1 : Matrix (Fin m) (Fin m) ℂ) ρ =
      lop !![(1 : ℂ), z; 0, 1] (1 : Matrix (Fin m) (Fin m) ℂ)
        (lop (Matrix.of ![r, s]) (1 : Matrix (Fin m) (Fin m) ℂ) ρ) := by
    rw [lop_lop, Matrix.one_mul]
  rw [← shear_rows, ← lop_apply_00, e, lop_rows_eq_blk hH, blkOf_lop_shear]
  simp

/-- For positive `P` and `Q`, `(P + Q) w = 0` forces `P w = 0` and `Q w = 0`. -/
theorem mulVec_eq_zero_of_add {ι : Type*} [Fintype ι] [DecidableEq ι] {P Q : Matrix ι ι ℂ}
    (hP : IsPSD P) (hQ : IsPSD Q) {w : ι → ℂ} (h : (P + Q) *ᵥ w = 0) : P *ᵥ w = 0 ∧ Q *ᵥ w = 0 := by
  have hq : star w ⬝ᵥ (P *ᵥ w) + star w ⬝ᵥ (Q *ᵥ w) = 0 := by
    rw [← dotProduct_add, ← add_mulVec, h, dotProduct_zero]
  have hre := congrArg Complex.re hq
  rw [Complex.add_re, Complex.zero_re] at hre
  have h1 := (hP w).1
  have h2 := (hQ w).1
  exact ⟨isPSD_mulVec_eq_zero hP (Complex.ext (by simp; linarith) (hP w).2),
    isPSD_mulVec_eq_zero hQ (Complex.ext (by simp; linarith) (hQ w).2)⟩

/-- **The shear on two rows**: for a PPT ρ and rows `r, s`, some `z` makes every kernel vector of
`X(r + z s)` a kernel vector of both `X(r)` and `X(s)`. -/
theorem exists_shear_rows {ρ : Mat n m} (hρ : IsPPT ρ) (r s : Fin n → ℂ) :
    ∃ z : ℝ, ∀ w, xBlock ρ (r + (z : ℂ) • s) *ᵥ w = 0 → xBlock ρ r *ᵥ w = 0 ∧ xBlock ρ s *ᵥ w = 0 := by
  have hH : ρᴴ = ρ := hρ.1.hermitian
  have hσ : IsPPT (blk (xBlock ρ r) (cross ρ r s) (cross ρ r s)ᴴ (xBlock ρ s)) := by
    rw [← lop_rows_eq_blk hH]
    exact isPPT_lop _ _ hρ
  obtain ⟨z, hz⟩ := exists_shear_ker hσ
  refine ⟨z, fun w hw => ?_⟩
  rw [xBlock_add_smul hH r s (z : ℂ)] at hw
  exact mulVec_eq_zero_of_add (isPSD_xBlock hρ.1 r) (isPSD_xBlock hρ.1 s) (hz w hw)

/-- **A row that sees all of ρ_B**: for a PPT ρ on `ℂᵏ⁺¹ ⊗ ℂᵐ` there is a row `r` with `r₀ = 1` and
`ker X(r) ⊆ ker ρ_B`. Shear in the rows one at a time. -/
theorem exists_row {k : ℕ} {ρ : Mat (k + 1) m} (hρ : IsPPT ρ) :
    ∃ r : Fin (k + 1) → ℂ, r 0 = 1 ∧ ∀ w, xBlock ρ r *ᵥ w = 0 → redB ρ *ᵥ w = 0 := by
  have step : ∀ j, j ≤ k → ∃ r : Fin (k + 1) → ℂ, r 0 = 1 ∧ ∀ w, xBlock ρ r *ᵥ w = 0 →
      ∀ a : Fin (k + 1), a.val ≤ j → xBlock ρ (Pi.single a 1) *ᵥ w = 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨Pi.single 0 1, by simp, fun w hw a ha => ?_⟩
      obtain rfl : a = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      exact hw
    | succ j ih =>
      intro hj
      obtain ⟨r, hr0, hr⟩ := ih (by omega)
      set a' : Fin (k + 1) := ⟨j + 1, by omega⟩ with ha'
      obtain ⟨z, hz⟩ := exists_shear_rows hρ r (Pi.single a' 1)
      have ha0 : (0 : Fin (k + 1)) ≠ a' := fun h => by
        have := congrArg Fin.val h
        simp [ha'] at this
      refine ⟨r + (z : ℂ) • Pi.single a' 1, by simp [hr0, ha0], fun w hw a ha => ?_⟩
      obtain ⟨h1, h2⟩ := hz w hw
      rcases Nat.lt_or_ge a.val (j + 1) with hlt | hge
      · exact hr w h1 a (by omega)
      · obtain rfl : a = a' := Fin.ext (by simp [ha']; omega)
        exact h2
  obtain ⟨r, hr0, hr⟩ := step k le_rfl
  refine ⟨r, hr0, fun w hw => ?_⟩
  rw [redB_eq_sum_xBlock, Matrix.sum_mulVec]
  exact Finset.sum_eq_zero fun a _ => hr w hw a (Nat.lt_succ_iff.1 a.2)

/-! ## Part 2. The normal form -/

/-- The `(a, b)` block of ρ. -/
def blkAt (ρ : Mat n m) (a b : Fin n) : Matrix (Fin m) (Fin m) ℂ := fun k l => ρ (a, k) (b, l)

theorem blkAt_lop_one {m' : ℕ} (M : Matrix (Fin m') (Fin m) ℂ) (ρ : Mat n m) (a b : Fin n) :
    blkAt (lop (1 : Matrix (Fin n) (Fin n) ℂ) M ρ) a b = M * blkAt ρ a b * Mᴴ := by
  ext k l
  simp only [blkAt, lop_one_apply, Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem redB_lop_one {m' : ℕ} (M : Matrix (Fin m') (Fin m) ℂ) (ρ : Mat n m) :
    redB (lop (1 : Matrix (Fin n) (Fin n) ℂ) M ρ) = M * redB ρ * Mᴴ := by
  rw [redB_eq_sum_xBlock, redB_eq_sum_xBlock, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [xBlock_single, xBlock_single]
  exact blkAt_lop_one M ρ a a

/-- The row operation with first row `r`; its other rows are those of the identity. -/
def rowOp {k : ℕ} (r : Fin (k + 1) → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun i j => if i = 0 then r j else (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j

/-- The inverse row operation when `r₀ = 1`: its first row is `(1, -r₁, …, -r_k)`. -/
def rowOpInv {k : ℕ} (r : Fin (k + 1) → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun i j => if i = 0 then (if j = 0 then 1 else -r j) else (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j

theorem rowOpInv_mul {k : ℕ} {r : Fin (k + 1) → ℂ} (hr : r 0 = 1) : rowOpInv r * rowOp r = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [rowOp, rowOpInv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, hr, Fin.succ_ne_zero,
      (Fin.succ_ne_zero _).symm]

theorem blkAt_lop_rowOp {k : ℕ} (r : Fin (k + 1) → ℂ) (ρ : Mat (k + 1) m) :
    blkAt (lop (rowOp r) (1 : Matrix (Fin m) (Fin m) ℂ) ρ) 0 0 = xBlock ρ r := by
  ext i j
  simp [blkAt, lop_apply_one, rowOp, xBlock]

/-- **Normal form**: when ρ is PPT on `ℂᵏ⁺¹ ⊗ ℂᵐ` and ρ_B is invertible, an invertible local operation
makes the `(0, 0)` block of ρ equal to 1. The row `r` of `exists_row` has `X(r)` invertible; the row
operation with first row `r`, then `1 ⊗ (Fᴴ)⁻¹` for a Gram factor `F` of `X(r)`, does it. -/
theorem exists_normal_form {k : ℕ} {ρ : Mat (k + 1) m} (hρ : IsPPT ρ) (hB : (redB ρ).det ≠ 0) :
    ∃ (G G' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (M M' : Matrix (Fin m) (Fin m) ℂ),
      blkAt (lop G M ρ) 0 0 = 1 ∧ lop G' M' (lop G M ρ) = ρ := by
  obtain ⟨r, hr0, hr⟩ := exists_row hρ
  have hX : (xBlock ρ r).det ≠ 0 := fun h0 => by
    obtain ⟨w, hw, hw0⟩ := exists_mulVec_eq_zero_iff.2 h0
    exact hw (eq_zero_of_mulVec_eq_zero hB (hr w hw0))
  obtain ⟨F, hF⟩ := (isPSD_xBlock hρ.1 r).gram
  have hFdet : IsUnit F.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hX
    rw [hF, det_mul, det_conjTranspose, h0, mul_zero]
  have hFHdet : IsUnit Fᴴ.det := by
    rw [det_conjTranspose]
    exact hFdet.star
  set M : Matrix (Fin m) (Fin m) ℂ := (Fᴴ)⁻¹ with hM
  have hMM : Fᴴ * M = 1 := mul_nonsing_inv _ hFHdet
  have hMM' : M * Fᴴ = 1 := nonsing_inv_mul _ hFHdet
  have hMH : Mᴴ = F⁻¹ := by rw [hM, conjTranspose_nonsing_inv, conjTranspose_conjTranspose]
  refine ⟨rowOp r, rowOpInv r, M, Fᴴ, ?_, ?_⟩
  · have e : lop (rowOp r) M ρ = lop (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) M
        (lop (rowOp r) (1 : Matrix (Fin m) (Fin m) ℂ) ρ) := by
      rw [lop_lop, Matrix.one_mul, Matrix.mul_one]
    rw [e, blkAt_lop_one, blkAt_lop_rowOp, hF, hMH, ← Matrix.mul_assoc, hMM', Matrix.one_mul,
      mul_nonsing_inv _ hFdet]
  · rw [lop_lop, rowOpInv_mul hr0, hMM, lop_one]

/-! ## Part 3. Rank m forces a Gram form -/

/-- **Rank m forces a Gram form**: if ρ is Hermitian, its `(0, 0)` block is 1 and its rank is at most m,
then every block is `ρ_ab = B_aᴴ B_b`, with `B_a` the `(0, a)` block. The m columns through the
`(0, 0)` block are independent, so they span the column space. -/
theorem blkAt_eq_gram {k : ℕ} {ρ : Mat (k + 1) m} (hH : ρᴴ = ρ) (h1 : blkAt ρ 0 0 = 1)
    (hr : ρ.rank ≤ m) (a b : Fin (k + 1)) : blkAt ρ a b = (blkAt ρ 0 a)ᴴ * blkAt ρ 0 b := by
  have h1' : ∀ i j, ρ (0, i) (0, j) = (1 : Matrix (Fin m) (Fin m) ℂ) i j := fun i j =>
    congrFun (congrFun h1 i) j
  have hρ : ∀ x y, ρ x y = star (ρ y x) := fun x y => by
    have := congrFun (congrFun hH x) y
    rw [conjTranspose_apply] at this
    exact this.symm
  have hli : LinearIndependent ℂ (fun l : Fin m => ρ.col (0, l)) := by
    refine Fintype.linearIndependent_iff.2 fun g hg l => ?_
    have := congrFun hg (0, l)
    simpa [Finset.sum_apply, col_apply, h1', Matrix.one_apply] using this
  have hle : Submodule.span ℂ (Set.range fun l : Fin m => ρ.col (0, l)) ≤
      Submodule.span ℂ (Set.range ρ.col) :=
    Submodule.span_mono (Set.range_subset_iff.2 fun l => ⟨(0, l), rfl⟩)
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [← rank_eq_finrank_span_cols, finrank_span_eq_card hli, Fintype.card_fin]
    exact hr)
  ext i j
  have hmem : ρ.col (b, j) ∈ Submodule.span ℂ (Set.range fun l : Fin m => ρ.col (0, l)) := by
    rw [heq]
    exact Submodule.subset_span ⟨(b, j), rfl⟩
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  have hβ0 : ∀ l, β l = ρ (0, l) (b, j) := fun l => by
    have := congrFun hβ (0, l)
    simpa [Finset.sum_apply, col_apply, h1', Matrix.one_apply] using this
  have := congrFun hβ (a, i)
  simp only [Finset.sum_apply, Pi.smul_apply, col_apply, smul_eq_mul, hβ0] at this
  simp only [blkAt, Matrix.mul_apply, conjTranspose_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun l _ => by rw [hρ (a, i) (0, l)]; ring

/-! ## Part 4. PPT makes the blocks commute -/

/-- **A PPT corner form `[[1, N], [Nᴴ, Nᴴ N]]` has N normal**: PPT gives `Nᴴ N ⪰ N Nᴴ`, and the difference
has trace zero. -/
theorem normal_of_ppt_corner {N : Matrix (Fin m) (Fin m) ℂ} (h : IsPSD (pt (blk 1 N Nᴴ (Nᴴ * N)))) :
    Nᴴ * N = N * Nᴴ := by
  have hS := isPSD_of_transpose (isPSD_schur_pt h)
  exact sub_eq_zero.1 (eq_zero_of_isPSD_trace hS (by rw [trace_sub, trace_mul_comm, sub_self]))

theorem xBlock_eq_sum (ρ : Mat n m) (s : Fin n → ℂ) :
    xBlock ρ s = ∑ a, ∑ b, (s a * star (s b)) • blkAt ρ a b := by
  ext k l
  simp only [xBlock, blkAt, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem cross_single_left (ρ : Mat n m) (a₀ : Fin n) (s : Fin n → ℂ) :
    cross ρ (Pi.single a₀ 1) s = ∑ b, star (s b) • blkAt ρ a₀ b := by
  ext k l
  simp [cross, blkAt, Matrix.sum_apply, Pi.single_apply, Finset.sum_ite_irrel]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem sum_single_smul {κ : Type*} [Fintype κ] [DecidableEq κ] (B : κ → Matrix (Fin m) (Fin m) ℂ)
    (a : κ) (x : ℂ) : ∑ b, (Pi.single a x : κ → ℂ) b • B b = x • B a := by
  simp [Pi.single_apply, ite_smul]

/-- **Every combination of the blocks is normal**: compress to the rows `e₀` and `s`, which gives the
corner form `[[1, N], [Nᴴ, Nᴴ N]]` for `N = Σ_b conj(s_b) B_b`. -/
theorem normal_comb {k : ℕ} {ρ : Mat (k + 1) m} (hρ : IsPPT ρ) (h1 : blkAt ρ 0 0 = 1)
    (hg : ∀ a b, blkAt ρ a b = (blkAt ρ 0 a)ᴴ * blkAt ρ 0 b) (c : Fin (k + 1) → ℂ) :
    (∑ b, c b • blkAt ρ 0 b)ᴴ * (∑ b, c b • blkAt ρ 0 b) =
      (∑ b, c b • blkAt ρ 0 b) * (∑ b, c b • blkAt ρ 0 b)ᴴ := by
  set N := ∑ b, c b • blkAt ρ 0 b with hN
  set s : Fin (k + 1) → ℂ := fun b => star (c b) with hs
  have hX0 : xBlock ρ (Pi.single 0 1) = 1 := by rw [xBlock_single]; exact h1
  have hC : cross ρ (Pi.single 0 1) s = N := by
    rw [cross_single_left, hN]
    simp [hs]
  have hXs : xBlock ρ s = Nᴴ * N := by
    rw [xBlock_eq_sum, hN, conjTranspose_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hg a b, conjTranspose_smul, smul_mul_smul_comm]
    simp [hs]
  have hσ := isPPT_lop (Matrix.of ![Pi.single 0 1, s]) (1 : Matrix (Fin m) (Fin m) ℂ) hρ
  rw [lop_rows_eq_blk hρ.1.hermitian, hX0, hC, hXs] at hσ
  exact normal_of_ppt_corner hσ.2

/-- The normality defect of `A + c B`, expanded. -/
theorem cross_of_normal {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : Aᴴ * A = A * Aᴴ) (hB : Bᴴ * B = B * Bᴴ) (c : ℂ)
    (h : (A + c • B)ᴴ * (A + c • B) = (A + c • B) * (A + c • B)ᴴ) :
    c • (Aᴴ * B - B * Aᴴ) + star c • (Bᴴ * A - A * Bᴴ) = 0 := by
  have e : (A + c • B)ᴴ * (A + c • B) - (A + c • B) * (A + c • B)ᴴ =
      (Aᴴ * A - A * Aᴴ) + (star c * c) • (Bᴴ * B - B * Bᴴ) +
        (c • (Aᴴ * B - B * Aᴴ) + star c • (Bᴴ * A - A * Bᴴ)) := by
    simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_smul, smul_sub, mul_comm c (star c)]
    abel
  rw [sub_eq_zero.2 h, sub_eq_zero.2 hA, sub_eq_zero.2 hB, smul_zero, zero_add, zero_add] at e
  exact e.symm

theorem eq_zero_of_add_of_smul_I {V : Type*} [AddCommGroup V] [Module ℂ V] {X Y : V} (h1 : X + Y = 0)
    (hI : Complex.I • X + star Complex.I • Y = 0) : X = 0 := by
  rw [eq_neg_of_add_eq_zero_right h1, Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_neg,
    ← add_smul] at hI
  exact (smul_eq_zero.1 hI).resolve_left (by
    rw [← two_mul]
    exact mul_ne_zero two_ne_zero Complex.I_ne_zero)

/-- **Normal combinations commute**: if `A`, `B`, `A + B` and `A + i B` are normal, then `Aᴴ B = B Aᴴ`. -/
theorem comm_of_normal {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : Aᴴ * A = A * Aᴴ) (hB : Bᴴ * B = B * Bᴴ) (h1 : (A + B)ᴴ * (A + B) = (A + B) * (A + B)ᴴ)
    (hI : (A + Complex.I • B)ᴴ * (A + Complex.I • B) = (A + Complex.I • B) * (A + Complex.I • B)ᴴ) :
    Aᴴ * B = B * Aᴴ := by
  have e1 := cross_of_normal hA hB 1 (by rwa [one_smul])
  simp only [one_smul, star_one] at e1
  exact sub_eq_zero.1 (eq_zero_of_add_of_smul_I e1 (cross_of_normal hA hB Complex.I hI))

/-- **The blocks commute**: `B_aᴴ B_b = B_b B_aᴴ` for all a, b. -/
theorem comm_blocks {k : ℕ} {ρ : Mat (k + 1) m} (hρ : IsPPT ρ) (h1 : blkAt ρ 0 0 = 1)
    (hg : ∀ a b, blkAt ρ a b = (blkAt ρ 0 a)ᴴ * blkAt ρ 0 b) (a b : Fin (k + 1)) :
    (blkAt ρ 0 a)ᴴ * blkAt ρ 0 b = blkAt ρ 0 b * (blkAt ρ 0 a)ᴴ := by
  have hN := normal_comb hρ h1 hg
  have e : ∀ x : ℂ, ∑ c, (Pi.single a 1 + Pi.single b x : Fin (k + 1) → ℂ) c • blkAt ρ 0 c =
      blkAt ρ 0 a + x • blkAt ρ 0 b := fun x => by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, sum_single_smul, one_smul]
  have hA := hN (Pi.single a 1)
  have hB := hN (Pi.single b 1)
  have h1' := hN (Pi.single a 1 + Pi.single b 1 : Fin (k + 1) → ℂ)
  have hI := hN (Pi.single a 1 + Pi.single b Complex.I : Fin (k + 1) → ℂ)
  rw [sum_single_smul, one_smul] at hA hB
  rw [e, one_smul] at h1'
  rw [e] at hI
  exact comm_of_normal hA hB h1' hI

/-! ## Part 5. Commuting blocks give a separable operator -/

/-- **A Gram form with commuting normal blocks is separable**: Fuglede's theorem makes the blocks
commute, they diagonalize in one orthonormal basis `U`, and
`ρ = Σ_p (conj d_p ⊗ U_p)(conj d_p ⊗ U_p)†`. -/
theorem sep_of_gram_comm {k : ℕ} {ρ : Mat (k + 1) m} (B : Fin (k + 1) → Matrix (Fin m) (Fin m) ℂ)
    (hg : ∀ a b, blkAt ρ a b = (B a)ᴴ * B b) (hc : ∀ a b, (B a)ᴴ * B b = B b * (B a)ᴴ) :
    IsSeparable ρ := by
  have h1 : ∀ a b, B a * B b = B b * B a := fun a b => by
    have h := congrArg conjTranspose (MathLab.fuglede (hc b b) (hc a b))
    simp only [conjTranspose_mul, conjTranspose_conjTranspose] at h
    exact h.symm
  obtain ⟨U, d, hUU, -, hd⟩ := MathLab.normal_spectral_family B h1 hc
  have hprod : ∀ a b, (B a)ᴴ * B b = U * diagonal (fun p => star (d a p) * d b p) * Uᴴ := fun a b => by
    rw [hd a, hd b, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _),
      diagonal_mul_diagonal]
    rfl
  have hρ : ρ = ∑ p, vecMulVec (prodVec (fun a => star (d a p)) (fun i => U i p))
      (star (prodVec (fun a => star (d a p)) (fun i => U i p))) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    have h := congrFun (congrFun (hg a b) i) j
    rw [hprod] at h
    simp only [blkAt] at h
    rw [h, Matrix.mul_apply]
    simp only [mul_diagonal, conjTranspose_apply, Matrix.sum_apply, vecMulVec_apply, prodVec, Pi.star_apply,
      star_mul', star_star]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hρ]
  exact isSeparable_of_fintype _ _

/-- **Normalized PPT operators of rank m are separable**: a PPT ρ on `ℂᵏ⁺¹ ⊗ ℂᵐ` with `(0, 0)` block 1
and rank at most m. -/
theorem sep_of_normalized {k : ℕ} {ρ : Mat (k + 1) m} (hρ : IsPPT ρ) (h1 : blkAt ρ 0 0 = 1)
    (hr : ρ.rank ≤ m) : IsSeparable ρ := by
  have hg := blkAt_eq_gram hρ.1.hermitian h1 hr
  exact sep_of_gram_comm (blkAt ρ 0) hg (comm_blocks hρ h1 hg)

/-! ## Part 6. The theorem -/

theorem sep_of_rank_le_of_det {k : ℕ} {ρ : Mat (k + 1) m} (hρ : IsPPT ρ) (hB : (redB ρ).det ≠ 0)
    (hr : ρ.rank ≤ m) : IsSeparable ρ := by
  obtain ⟨G, G', M, M', h1, h2⟩ := exists_normal_form hρ hB
  rw [← h2]
  exact isSeparable_lop _ _
    (sep_of_normalized (isPPT_lop G M hρ) h1 ((ChainLowRank.rank_lop_le G M ρ).trans hr))

/-- **Horodecki, Lewenstein, Vidal and Cirac**: for all n and m, a PPT operator on `ℂⁿ ⊗ ℂᵐ` whose rank is
at most that of ρ_B is separable. Compress ℂᵐ to the support of ρ_B, where ρ_B is invertible. -/
theorem sep_of_rank_le_rank_redB {ρ : Mat n m} (hρ : IsPPT ρ) (hr : ρ.rank ≤ (redB ρ).rank) :
    IsSeparable ρ := by
  rcases n with _ | k
  · rw [show ρ = 0 from Matrix.ext fun x => x.1.elim0]
    exact isSeparable_zero
  obtain ⟨W, -, hker, hdet⟩ := exists_support (isPSD_redB hρ.1)
  have hH : ρᴴ = ρ := hρ.1.hermitian
  have hP : (W * Wᴴ)ᴴ = W * Wᴴ := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have h2 : ρ * ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) ⊗ₖ (W * Wᴴ)) = ρ := by
    have := mul_one_kron_eq_zero hρ.1 hker
    rw [kron_sub, one_kronecker_one, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have h4 : ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) ⊗ₖ (W * Wᴴ)) * ρ = ρ := by
    have := congrArg conjTranspose h2
    rwa [conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one, hP, hH] at this
  have hback : lop (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) W
      (lop (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) Wᴴ ρ) = ρ := by
    rw [lop_lop, Matrix.one_mul, lop, conjTranspose_kronecker, conjTranspose_one, hP, h4, h2]
  have hσ : IsPPT (lop (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) Wᴴ ρ) := isPPT_lop _ _ hρ
  have hdet' : (redB (lop (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) Wᴴ ρ)).det ≠ 0 := by
    rw [redB_lop_one, conjTranspose_conjTranspose]
    exact hdet
  rw [← hback]
  exact isSeparable_lop _ _ (sep_of_rank_le_of_det hσ hdet' ((ChainLowRank.rank_lop_le _ _ ρ).trans hr))

theorem isSeparable_swapM {ρ : Mat n m} (h : IsSeparable ρ) : IsSeparable (swapM ρ) := by
  obtain ⟨r, x, y, rfl⟩ := h
  refine ⟨r, y, x, ?_⟩
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [swapM, Matrix.sum_apply, vecMulVec_apply, prodVec, Pi.star_apply, star_mul']
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem redB_swapM (ρ : Mat n m) : redB (swapM ρ) = redA ρ := rfl

/-- **The same with ρ_A**, by swapping the factors. -/
theorem sep_of_rank_le_rank_redA {ρ : Mat n m} (hρ : IsPPT ρ) (hr : ρ.rank ≤ (redA ρ).rank) :
    IsSeparable ρ :=
  isSeparable_swapM (sep_of_rank_le_rank_redB (isPPT_swapM hρ) (by rw [rank_swapM, redB_swapM]; exact hr))

/-- **The theorem in its usual form**: a PPT operator whose rank is at most the larger rank of its reduced
operators is separable. -/
theorem sep_of_rank_le_max {ρ : Mat n m} (hρ : IsPPT ρ) (hr : ρ.rank ≤ max (redA ρ).rank (redB ρ).rank) :
    IsSeparable ρ := by
  rcases le_max_iff.1 hr with h | h
  · exact sep_of_rank_le_rank_redA hρ h
  · exact sep_of_rank_le_rank_redB hρ h

/-! ## Part 7. The minimal rank of PPT entanglement -/

/-- **Rank-three PPT states are separable** (Horodecki, Lewenstein, Vidal and Cirac 2000), in every
dimension. If a reduced operator has rank at least that of ρ, the theorem applies; otherwise both
reduced operators have rank at most two, and ρ lives on a 2 × 2 space. -/
theorem sep_of_rank_le_three {ρ : Mat n m} (hρ : IsPPT ρ) (hr : ρ.rank ≤ 3) : IsSeparable ρ := by
  by_cases hB : ρ.rank ≤ (redB ρ).rank
  · exact sep_of_rank_le_rank_redB hρ hB
  by_cases hA : ρ.rank ≤ (redA ρ).rank
  · exact sep_of_rank_le_rank_redA hρ hA
  exact sep_of_ranks_le_two hρ (by omega) (by omega)

/-- **The minimal rank of PPT entanglement is four**: every PPT operator of rank at most three is
separable, in every dimension, and the tiles state on `ℂ³ ⊗ ℂ³` is PPT, entangled and of rank four. -/
theorem min_rank_ppt_entangled :
    (∀ (n m : ℕ) (ρ : Mat n m), IsPPT ρ → ρ.rank ≤ 3 → IsSeparable ρ) ∧
      ∃ ρ : Mat 3 3, IsPPT ρ ∧ ¬ IsSeparable ρ ∧ ρ.rank = 4 :=
  ⟨fun _ _ _ h hr => sep_of_rank_le_three h hr, ChainTiles.tiles, ChainTiles.tiles_ppt_entangled⟩

/-- **Every PPT entangled operator has rank at least four.** -/
theorem four_le_rank {ρ : Mat n m} (hρ : IsPPT ρ) (hent : ¬ IsSeparable ρ) : 4 ≤ ρ.rank := by
  by_contra h
  exact hent (sep_of_rank_le_three hρ (by omega))

end ChainLowRankMN

end

end -- public section

#print axioms ChainLowRankMN.exists_row
#print axioms ChainLowRankMN.exists_normal_form
#print axioms ChainLowRankMN.blkAt_eq_gram
#print axioms ChainLowRankMN.comm_blocks
#print axioms ChainLowRankMN.sep_of_gram_comm
#print axioms ChainLowRankMN.sep_of_rank_le_rank_redB
#print axioms ChainLowRankMN.sep_of_rank_le_rank_redA
#print axioms ChainLowRankMN.sep_of_rank_le_max
#print axioms ChainLowRankMN.sep_of_rank_le_three
#print axioms ChainLowRankMN.min_rank_ppt_entangled
#print axioms ChainLowRankMN.four_le_rank

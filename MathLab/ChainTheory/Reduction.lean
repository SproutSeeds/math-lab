module

/-
Reduction.lean

**Rank-two PPT states are separable** in every dimension (P. Horodecki, Smolin, Terhal and Thapliyal,
Theor. Comput. Sci. 292 (2003) 589), through the reduction criterion and the rank inequality it gives.

  Part 1  Partial traces `ρ_A`, `ρ_B`. A positive ρ lives on (support of ρ_A) ⊗ (support of ρ_B).
  Part 2  The reduction criterion (M. and P. Horodecki 1999; Cerf, Adami and Gingrich 1999): a PPT
          operator satisfies `ρ ⪯ ρ_A ⊗ 1`, because `2 (ρ_A ⊗ 1 - ρ) = Σ_pq (1 ⊗ A_pq) ρ^Γ (1 ⊗ A_pq)ᴴ`
          for the antisymmetric units `A_pq = E_pq - E_qp`.
  Part 3  The rank inequality: a PPT operator has `rank ρ_A ≤ rank ρ` and `rank ρ_B ≤ rank ρ`. Write
          `ρ = Σᵢ ψᵢ ψᵢ†` over `rank ρ` terms; the Gram matrix `ψᵢ† (ρ_A⁻¹ ⊗ 1) ψⱼ` has trace `n` and,
          by the criterion, Frobenius norm squared at most `n`; Cauchy–Schwarz gives `n ≤ rank ρ`.
  Part 4  Rank two: both supports have dimension at most two, so ρ lives on ℂ² ⊗ ℂ², where the two-qubit
          theorem applies. The Bell state (rank one, ρ_A of rank two) shows PPT is needed.
-/
public import MathLab.ChainTheory.LowRank

@[expose] public section

open Matrix ComplexOrder Module
open scoped Kronecker

noncomputable section

namespace ChainReduction

open ChoiDark ChainReadCap ChainDuality ChainStormer ChainWoronowicz ChainPPT

variable {n m : ℕ}

/-! ## Part 1. Partial traces and supports -/

/-- The reduced operator on the first factor, `ρ_A = tr_B ρ`. -/
def redA (ρ : Mat n m) : Matrix (Fin n) (Fin n) ℂ := fun a b => ∑ k, ρ (a, k) (b, k)

/-- The reduced operator on the second factor, `ρ_B = tr_A ρ`. -/
def redB (ρ : Mat n m) : Matrix (Fin m) (Fin m) ℂ := fun k l => ∑ a, ρ (a, k) (a, l)

/-- `x† ρ_A x = Σ_k (x ⊗ e_k)† ρ (x ⊗ e_k)`. -/
theorem quad_redA (ρ : Mat n m) (x : Fin n → ℂ) :
    star x ⬝ᵥ (redA ρ *ᵥ x) =
      ∑ k, star (prodVec x (Pi.single k 1)) ⬝ᵥ (ρ *ᵥ prodVec x (Pi.single k 1)) := by
  simp only [dotProduct, mulVec, redA, prodVec, Pi.star_apply, Fintype.sum_prod_type, Pi.single_apply,
      apply_ite star, star_zero, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Finset.mul_sum, Finset.sum_mul]
  have hr : ∀ k a, (∑ j, ∑ b, if j = k then star (x a) * (ρ (a, j) (b, k) * x b) else 0) =
      ∑ b, star (x a) * (ρ (a, k) (b, k) * x b) := by
    intro k a
    rw [Finset.sum_eq_single k (fun j _ hj => Finset.sum_eq_zero fun b _ => ite_eq_right hj) (by simp)]
    simp
  simp only [hr]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

/-- `y† ρ_B y = Σ_a (e_a ⊗ y)† ρ (e_a ⊗ y)`. -/
theorem quad_redB (ρ : Mat n m) (y : Fin m → ℂ) :
    star y ⬝ᵥ (redB ρ *ᵥ y) =
      ∑ a, star (prodVec (Pi.single a 1) y) ⬝ᵥ (ρ *ᵥ prodVec (Pi.single a 1) y) := by
  simp only [dotProduct, mulVec, redB, prodVec, Pi.star_apply, Fintype.sum_prod_type, Pi.single_apply,
      apply_ite star, star_zero, mul_ite, ite_mul, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Finset.mul_sum, Finset.sum_mul, Finset.sum_ite_irrel,
      Finset.sum_const_zero]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

theorem isPSD_redA {ρ : Mat n m} (h : IsPSD ρ) : IsPSD (redA ρ) := fun x => by
  rw [quad_redA, Complex.re_sum, Complex.im_sum]
  exact ⟨Finset.sum_nonneg fun k _ => (h _).1, Finset.sum_eq_zero fun k _ => (h _).2⟩

theorem isPSD_redB {ρ : Mat n m} (h : IsPSD ρ) : IsPSD (redB ρ) := fun y => by
  rw [quad_redB, Complex.re_sum, Complex.im_sum]
  exact ⟨Finset.sum_nonneg fun a _ => (h _).1, Finset.sum_eq_zero fun a _ => (h _).2⟩

/-- A sum of complex numbers with nonnegative real parts and zero imaginary parts vanishes only termwise. -/
theorem eq_zero_of_sum_eq_zero {ι : Type*} (s : Finset ι) {f : ι → ℂ} (hre : ∀ i ∈ s, 0 ≤ (f i).re)
    (him : ∀ i ∈ s, (f i).im = 0) (h : ∑ i ∈ s, f i = 0) : ∀ i ∈ s, f i = 0 := by
  intro i hi
  have hr : ∑ j ∈ s, (f j).re = 0 := by rw [← Complex.re_sum, h, Complex.zero_re]
  exact Complex.ext ((Finset.sum_eq_zero_iff_of_nonneg hre).1 hr i hi) (him i hi)

/-- If `ρ_A x = 0`, then ρ kills every `x ⊗ e_k`. -/
theorem mulVec_prodVec_eq_zero {ρ : Mat n m} (h : IsPSD ρ) {x : Fin n → ℂ} (hx : redA ρ *ᵥ x = 0)
    (k : Fin m) : ρ *ᵥ prodVec x (Pi.single k 1) = 0 := by
  apply isPSD_mulVec_eq_zero h
  have hq := quad_redA ρ x
  rw [hx, dotProduct_zero] at hq
  exact eq_zero_of_sum_eq_zero Finset.univ (fun j _ => (h _).1) (fun j _ => (h _).2) hq.symm k
    (Finset.mem_univ k)

/-- If `ρ_B y = 0`, then ρ kills every `e_a ⊗ y`. -/
theorem mulVec_prodVec_eq_zero' {ρ : Mat n m} (h : IsPSD ρ) {y : Fin m → ℂ} (hy : redB ρ *ᵥ y = 0)
    (a : Fin n) : ρ *ᵥ prodVec (Pi.single a 1) y = 0 := by
  apply isPSD_mulVec_eq_zero h
  have hq := quad_redB ρ y
  rw [hy, dotProduct_zero] at hq
  exact eq_zero_of_sum_eq_zero Finset.univ (fun j _ => (h _).1) (fun j _ => (h _).2) hq.symm a
    (Finset.mem_univ a)

/-- **ρ lives on the support of ρ_A**: if `ρ_A K = 0`, then `ρ (K ⊗ 1) = 0`. -/
theorem mul_kron_one_eq_zero {n' : ℕ} {ρ : Mat n m} (h : IsPSD ρ) {K : Matrix (Fin n) (Fin n') ℂ}
    (hK : redA ρ * K = 0) : ρ * (K ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) = 0 := by
  ext x ⟨c, l⟩
  have hcol : redA ρ *ᵥ (fun a => K a c) = 0 := by
    ext a
    simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun (congrFun hK a) c
  have h0 := congrFun (mulVec_prodVec_eq_zero h hcol l) x
  simpa [Matrix.mul_apply, mulVec, dotProduct, prodVec, kroneckerMap_apply, Matrix.one_apply,
      Pi.single_apply, Fintype.sum_prod_type] using h0

/-- **ρ lives on the support of ρ_B**: if `ρ_B K = 0`, then `ρ (1 ⊗ K) = 0`. -/
theorem mul_one_kron_eq_zero {m' : ℕ} {ρ : Mat n m} (h : IsPSD ρ) {K : Matrix (Fin m) (Fin m') ℂ}
    (hK : redB ρ * K = 0) : ρ * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ K) = 0 := by
  ext x ⟨c, l⟩
  have hcol : redB ρ *ᵥ (fun k => K k l) = 0 := by
    ext k
    simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun (congrFun hK k) l
  have h0 := congrFun (mulVec_prodVec_eq_zero' h hcol c) x
  simpa [Matrix.mul_apply, mulVec, dotProduct, prodVec, kroneckerMap_apply, Matrix.one_apply,
      Pi.single_apply, Fintype.sum_prod_type] using h0

/-! ## Part 2. The reduction criterion -/

/-- The antisymmetric unit `A_pq = E_pq - E_qp`. -/
def asym (p q : Fin m) : Matrix (Fin m) (Fin m) ℂ := single p q 1 - single q p 1

theorem sum_asym (k k' l l' : Fin m) :
    ∑ p, ∑ q, asym p q k k' * star (asym p q l l') =
      2 * ((if k = l ∧ k' = l' then 1 else 0) - (if k = l' ∧ k' = l then 1 else 0)) := by
  simp only [asym, Matrix.sub_apply, Matrix.single_apply, star_sub, apply_ite star, star_one, star_zero,
      mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, ite_and, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Finset.sum_const_zero, Finset.sum_ite_irrel]
  by_cases h1 : k = l <;> by_cases h2 : k' = l' <;> by_cases h3 : k = l' <;> by_cases h4 : k' = l <;>
    simp_all [eq_comm] <;> norm_num

/-- The entries of a local operation on the second factor. -/
theorem lop_one_apply {m' : ℕ} (M : Matrix (Fin m') (Fin m) ℂ) (σ : Mat n m) (a b : Fin n)
    (k l : Fin m') :
    lop (1 : Matrix (Fin n) (Fin n) ℂ) M σ (a, k) (b, l) =
      ∑ k', ∑ l', M k k' * σ (a, k') (b, l') * star (M l l') := by
  simp only [lop, Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      apply_ite star, star_zero, mul_ite, mul_zero, Finset.sum_mul, Finset.sum_ite_irrel,
      Finset.sum_const_zero]
  rw [Finset.sum_comm]

theorem sum_four_comm {α ι κ : Type*} [AddCommMonoid α] [Fintype ι] [Fintype κ] (F : ι → ι → κ → κ → α) :
    ∑ p, ∑ q, ∑ i, ∑ j, F p q i j = ∑ i, ∑ j, ∑ p, ∑ q, F p q i j :=
  calc ∑ p, ∑ q, ∑ i, ∑ j, F p q i j = ∑ p, ∑ i, ∑ q, ∑ j, F p q i j :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ p, ∑ q, ∑ j, F p q i j := Finset.sum_comm
    _ = ∑ i, ∑ p, ∑ j, ∑ q, F p q i j :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ p, ∑ q, F p q i j := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- **The reduction identity**: `2 (ρ_A ⊗ 1 - ρ) = Σ_pq (1 ⊗ A_pq) ρ^Γ (1 ⊗ A_pq)ᴴ`. -/
theorem reduction_identity (ρ : Mat n m) :
    (2 : ℝ) • (redA ρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) - ρ) =
      ∑ p, ∑ q, lop (1 : Matrix (Fin n) (Fin n) ℂ) (asym p q) (pt ρ) := by
  ext ⟨a, k⟩ ⟨b, l⟩
  simp only [Matrix.sum_apply, lop_one_apply]
  rw [sum_four_comm (fun p q k' l' => asym p q k k' * pt ρ (a, k') (b, l') * star (asym p q l l'))]
  have e : ∀ k' l', ∑ p, ∑ q, asym p q k k' * pt ρ (a, k') (b, l') * star (asym p q l l') =
      pt ρ (a, k') (b, l') *
        (2 * ((if k = l ∧ k' = l' then 1 else 0) - (if k = l' ∧ k' = l then 1 else 0))) := by
    intro k' l'
    rw [← sum_asym, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
  simp only [e]
  simp only [Matrix.smul_apply, Matrix.sub_apply, kroneckerMap_apply, Matrix.one_apply, redA, pt,
      Complex.real_smul, mul_sub, mul_ite, ite_and, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, Finset.mul_sum]
  push_cast
  split_ifs
  · rw [Finset.sum_congr rfl fun i _ => mul_comm (2 : ℂ) (ρ (a, i) (b, i))]
    ring
  · ring

/-- **The reduction criterion**: a PPT operator satisfies `ρ ⪯ ρ_A ⊗ 1`. -/
theorem reduction_criterion {ρ : Mat n m} (h : IsPPT ρ) :
    IsPSD (redA ρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) - ρ) := by
  have h2 : IsPSD ((2 : ℝ) • (redA ρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) - ρ)) := by
    rw [reduction_identity]
    exact Finset.sum_induction _ IsPSD (fun _ _ => IsPSD.add) isPSD_zero fun p _ =>
      Finset.sum_induction _ IsPSD (fun _ _ => IsPSD.add) isPSD_zero fun q _ => isPSD_lop _ _ h.2
  have h3 := h2.smul (t := (1 / 2 : ℝ)) (by norm_num)
  rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h3

/-! ## Part 3. The rank inequality -/

/-- **A positive semidefinite matrix is a sum of `rank` rank-one terms**: `√λᵢ vᵢ` over the nonzero
eigenvalues. -/
theorem exists_sum_rank_one {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : IsPSD X) :
    ∃ (t : Finset ι) (ψ : ι → ι → ℂ), t.card = X.rank ∧ X = ∑ i ∈ t, vecMulVec (ψ i) (star (ψ i)) := by
  have hH : X.IsHermitian := hX.hermitian
  have hev : ∀ i, 0 ≤ hH.eigenvalues i := fun i => by
    rw [hH.eigenvalues_eq]
    exact (hX _).1
  refine ⟨Finset.univ.filter (fun i => hH.eigenvalues i ≠ 0),
    fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ) • ⇑(hH.eigenvectorBasis i), ?_, ?_⟩
  · rw [hH.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  · have hspec := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    ext x y
    conv_lhs => rw [hspec]
    simp only [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply, Pi.smul_apply, Pi.star_apply,
        smul_eq_mul, star_mul', Function.comp_apply, Matrix.star_apply, diagonal_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, IsHermitian.eigenvectorUnitary_apply]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hs : (((Real.sqrt (hH.eigenvalues c)) : ℝ) : ℂ) * star (((Real.sqrt (hH.eigenvalues c)) : ℝ) : ℂ) =
        (hH.eigenvalues c : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hev c)]
    split_ifs with h0
    · linear_combination (-((hH.eigenvectorBasis c) x * star ((hH.eigenvectorBasis c) y))) * hs
    · rw [not_not.1 h0]
      simp

/-- The pairing of `Q ⊗ 1` with ρ is `tr(Q ρ_A)`. -/
theorem pair_kron_one (Q : Matrix (Fin n) (Fin n) ℂ) (ρ : Mat n m) :
    pair (Q ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) ρ = (Q * redA ρ).trace := by
  simp only [pair, kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, redA, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_comm

theorem quad_rank_one {ι : Type*} [Fintype ι] (u w : ι → ℂ) :
    star w ⬝ᵥ (vecMulVec u (star u) *ᵥ w) = ((Complex.normSq (star u ⬝ᵥ w) : ℝ) : ℂ) := by
  have e : star w ⬝ᵥ (vecMulVec u (star u) *ᵥ w) = star (star u ⬝ᵥ w) * (star u ⬝ᵥ w) := by
    simp only [dotProduct, mulVec, vecMulVec_apply, Pi.star_apply, star_sum, star_mul', star_star,
        Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e, Complex.star_def, Complex.normSq_eq_conj_mul_self]

/-- **The reduction criterion bounds the rank** (P. Horodecki, Smolin, Terhal and Thapliyal): if `ρ ⪰ 0`,
`ρ ⪯ ρ_A ⊗ 1` and `ρ_A` is invertible on `ℂⁿ`, then `n ≤ rank ρ`. -/
theorem le_rank_of_reduction {ρ : Mat n m} (hρ : IsPSD ρ)
    (hR : IsPSD (redA ρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) - ρ)) (hA : (redA ρ).det ≠ 0) :
    n ≤ ρ.rank := by
  obtain ⟨t, ψ, ht, hdec⟩ := exists_sum_rank_one hρ
  have hu : IsUnit (redA ρ).det := isUnit_iff_ne_zero.2 hA
  set Q : Matrix (Fin n) (Fin n) ℂ := (redA ρ)⁻¹ with hQ
  have hQA : Q * redA ρ = 1 := nonsing_inv_mul _ hu
  have hQH : Qᴴ = Q := by rw [hQ, conjTranspose_nonsing_inv, (isPSD_redA hρ).hermitian]
  set K : Mat n m := Q ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) with hK
  have hKH : Kᴴ = K := by rw [hK, conjTranspose_kronecker, hQH, conjTranspose_one]
  have hKAK : K * (redA ρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * K = K := by
    rw [hK, ← mul_kronecker_mul, ← mul_kronecker_mul, hQA, Matrix.one_mul, Matrix.one_mul, Matrix.one_mul]
  set G : Idx n m → Idx n m → ℂ := fun i j => star (ψ i) ⬝ᵥ (K *ᵥ ψ j) with hG
  have hcrit : ∀ j, ∑ i ∈ t, Complex.normSq (G i j) ≤ (G j j).re := by
    intro j
    have h0 := (hR (K *ᵥ ψ j)).1
    have e1 : star (K *ᵥ ψ j) ⬝ᵥ ((redA ρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ (K *ᵥ ψ j)) = G j j := by
      rw [star_mulVec, hKH, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hKAK]
    have e2 : star (K *ᵥ ψ j) ⬝ᵥ (ρ *ᵥ (K *ᵥ ψ j)) = ∑ i ∈ t, ((Complex.normSq (G i j) : ℝ) : ℂ) := by
      rw [hdec, Matrix.sum_mulVec, dotProduct_sum]
      exact Finset.sum_congr rfl fun i _ => quad_rank_one (ψ i) (K *ᵥ ψ j)
    rw [sub_mulVec, dotProduct_sub, Complex.sub_re, e1, e2, Complex.re_sum] at h0
    simp only [Complex.ofReal_re] at h0
    linarith
  have htr : ∑ j ∈ t, G j j = n := by
    have h : ∑ j ∈ t, G j j = pair K ρ := by
      rw [hdec, pair_sum_right]
      exact Finset.sum_congr rfl fun j _ => (pair_rank_one K (ψ j)).symm
    rw [h, hK, pair_kron_one, hQA, Matrix.trace_one, Fintype.card_fin]
  set g : Idx n m → ℝ := fun j => (G j j).re with hg
  have hsum : ∑ j ∈ t, g j = n := by
    have h := congrArg Complex.re htr
    rwa [Complex.re_sum, Complex.natCast_re] at h
  have hsq : ∀ j ∈ t, g j ^ 2 ≤ g j := by
    intro j hj
    have h1 : g j ^ 2 ≤ Complex.normSq (G j j) := by
      rw [Complex.normSq_apply]
      nlinarith [sq_nonneg (G j j).im]
    have h2 : Complex.normSq (G j j) ≤ ∑ i ∈ t, Complex.normSq (G i j) :=
      Finset.single_le_sum (f := fun i => Complex.normSq (G i j)) (fun i _ => Complex.normSq_nonneg _) hj
    linarith [hcrit j]
  have hsq_sum : ∑ j ∈ t, g j ^ 2 ≤ n := by
    rw [← hsum]
    exact Finset.sum_le_sum hsq
  have hcs := sq_sum_le_card_mul_sum_sq (s := t) (f := g)
  rw [hsum, ht] at hcs
  have hr : (0 : ℝ) ≤ ρ.rank := Nat.cast_nonneg _
  have key : (n : ℝ) ^ 2 ≤ ρ.rank * n := hcs.trans (mul_le_mul_of_nonneg_left hsq_sum hr)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · omega
  · have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hpos
    have : (n : ℝ) ≤ ρ.rank := by nlinarith
    exact_mod_cast this

/-- **The support of a positive semidefinite matrix**: an isometry `W` onto the span of the eigenvectors
with nonzero eigenvalues, `r = rank X` columns, with `X (1 - W Wᴴ) = 0` and `Wᴴ X W` invertible. -/
theorem exists_support {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ} (hX : IsPSD X) :
    ∃ W : Matrix (Fin k) (Fin X.rank) ℂ, Wᴴ * W = 1 ∧ X * (1 - W * Wᴴ) = 0 ∧ (Wᴴ * X * W).det ≠ 0 := by
  have hH : X.IsHermitian := hX.hermitian
  set U : Matrix (Fin k) (Fin k) ℂ := (hH.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hXU : ∀ x i, (X * U) x i = (hH.eigenvalues i : ℂ) * U x i := by
    intro x i
    have h := congrFun (hH.mulVec_eigenvectorBasis i) x
    rw [Matrix.mul_apply]
    simpa [hU, mulVec, dotProduct, Complex.real_smul] using h
  have hspec : ∀ x y, X x y = ∑ i, U x i * (hH.eigenvalues i : ℂ) * star (U y i) := by
    intro x y
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    conv_lhs => rw [h]
    simp [hU, Matrix.mul_apply, diagonal_apply, Matrix.star_apply]
  have hT : Fintype.card {i // hH.eigenvalues i ≠ 0} = X.rank := hH.rank_eq_card_non_zero_eigs.symm
  set e : Fin X.rank ≃ {i // hH.eigenvalues i ≠ 0} := (Fintype.equivFinOfCardEq hT).symm with he
  set f : Fin X.rank → Fin k := fun c => (e c).1 with hf
  have hfi : Function.Injective f := Subtype.val_injective.comp e.injective
  set W : Matrix (Fin k) (Fin X.rank) ℂ := Matrix.of fun x c => U x (f c) with hW
  have hUUe : ∀ i j, ∑ x, star (U x i) * U x j = if i = j then 1 else 0 := fun i j => by
    have h := congrFun (congrFun hUU i) j
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h
  refine ⟨W, ?_, ?_, ?_⟩
  · ext c c'
    simp only [hW, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, Matrix.one_apply, hUUe,
        hfi.eq_iff]
  · ext x y
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, Matrix.zero_apply, sub_eq_zero,
      ← Matrix.mul_assoc, Matrix.mul_apply]
    have hXW : ∀ c, (X * W) x c = (hH.eigenvalues (f c) : ℂ) * U x (f c) := fun c => by
      rw [← hXU, Matrix.mul_apply, Matrix.mul_apply]
      rfl
    simp only [hXW]
    simp only [conjTranspose_apply, hW, Matrix.of_apply]
    rw [hspec x y]
    set g : Fin k → ℂ := fun i => U x i * (hH.eigenvalues i : ℂ) * star (U y i) with hg
    have h5 : ∑ c, g (f c) = ∑ i, g i := by
      rw [← Finset.sum_image (s := Finset.univ) (g := f) (f := g) fun a _ b _ h => hfi h]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have h0 : hH.eigenvalues i = 0 := by
        by_contra hne
        exact hi (Finset.mem_image.2 ⟨e.symm ⟨i, hne⟩, Finset.mem_univ _, by simp [hf]⟩)
      simp [hg, h0]
    rw [← h5]
    exact Finset.sum_congr rfl fun c _ => by simp only [hg]; ring
  · have hdiag : Wᴴ * X * W = diagonal (fun c => (hH.eigenvalues (f c) : ℂ)) := by
      ext c c'
      have h1 : (Wᴴ * X * W) c c' = ∑ x, star (U x (f c)) * (X * U) x (f c') := by
        rw [Matrix.mul_assoc, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [conjTranspose_apply, hW, Matrix.of_apply, Matrix.mul_apply]
      rw [h1]
      simp only [hXU]
      calc ∑ x, star (U x (f c)) * ((hH.eigenvalues (f c') : ℂ) * U x (f c'))
          = (hH.eigenvalues (f c') : ℂ) * ∑ x, star (U x (f c)) * U x (f c') := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
        _ = diagonal (fun c => (hH.eigenvalues (f c) : ℂ)) c c' := by
            rw [hUUe, diagonal_apply]
            by_cases h : c = c'
            · subst h
              simp
            · simp [h, hfi.ne h]
    rw [hdiag, det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun c _ => Complex.ofReal_ne_zero.2 (e c).2

/-- The entries of a local operation on the first factor. -/
theorem lop_apply_one {n' : ℕ} (G : Matrix (Fin n') (Fin n) ℂ) (σ : Mat n m) (a b : Fin n')
    (k l : Fin m) :
    lop G (1 : Matrix (Fin m) (Fin m) ℂ) σ (a, k) (b, l) =
      ∑ a', ∑ b', G a a' * σ (a', k) (b', l) * star (G b b') := by
  simp only [lop, Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, apply_ite star, star_zero, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem redA_lop {n' : ℕ} (G : Matrix (Fin n') (Fin n) ℂ) (ρ : Mat n m) :
    redA (lop G (1 : Matrix (Fin m) (Fin m) ℂ) ρ) = G * redA ρ * Gᴴ := by
  ext a b
  simp only [redA, lop_apply_one, Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  calc ∑ k, ∑ a', ∑ b', G a a' * ρ (a', k) (b', k) * star (G b b')
      = ∑ a', ∑ k, ∑ b', G a a' * ρ (a', k) (b', k) * star (G b b') := Finset.sum_comm
    _ = ∑ a', ∑ b', ∑ k, G a a' * ρ (a', k) (b', k) * star (G b b') :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Swapping the two factors. -/
def swapM (ρ : Mat n m) : Mat m n := fun x y => ρ (x.2, x.1) (y.2, y.1)

theorem rank_swapM (ρ : Mat n m) : (swapM ρ).rank = ρ.rank :=
  rank_submatrix ρ (Equiv.prodComm (Fin m) (Fin n)) (Equiv.prodComm (Fin m) (Fin n))

theorem isPSD_swapM {ρ : Mat n m} (h : IsPSD ρ) : IsPSD (swapM ρ) := fun v => by
  have e : star v ⬝ᵥ (swapM ρ *ᵥ v) = star (v ∘ Prod.swap) ⬝ᵥ (ρ *ᵥ (v ∘ Prod.swap)) := by
    simp only [dotProduct, mulVec, swapM, Function.comp_apply, Pi.star_apply]
    rw [← (Equiv.prodComm (Fin n) (Fin m)).sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← (Equiv.prodComm (Fin n) (Fin m)).sum_comp]
    rfl
  rw [e]
  exact h _

theorem pt_swapM (ρ : Mat n m) : pt (swapM ρ) = swapM (pt ρ)ᵀ := rfl

theorem isPPT_swapM {ρ : Mat n m} (h : IsPPT ρ) : IsPPT (swapM ρ) :=
  ⟨isPSD_swapM h.1, by rw [pt_swapM]; exact isPSD_swapM (isPSD_transpose h.2)⟩

theorem redA_swapM (ρ : Mat n m) : redA (swapM ρ) = redB ρ := rfl

/-- **A PPT operator has rank at least that of ρ_A**: compress ℂⁿ to the support of ρ_A, where ρ_A is
invertible, and apply the reduction criterion there. -/
theorem rank_redA_le {ρ : Mat n m} (h : IsPPT ρ) : (redA ρ).rank ≤ ρ.rank := by
  obtain ⟨W, -, -, hdet⟩ := exists_support (isPSD_redA h.1)
  have hσ := isPPT_lop Wᴴ (1 : Matrix (Fin m) (Fin m) ℂ) h
  have hred : redA (lop Wᴴ (1 : Matrix (Fin m) (Fin m) ℂ) ρ) = Wᴴ * redA ρ * W := by
    rw [redA_lop, conjTranspose_conjTranspose]
  have := le_rank_of_reduction hσ.1 (reduction_criterion hσ) (by rw [hred]; exact hdet)
  exact this.trans (ChainLowRank.rank_lop_le _ _ _)

/-- **A PPT operator has rank at least that of ρ_B**, by swapping the factors. -/
theorem rank_redB_le {ρ : Mat n m} (h : IsPPT ρ) : (redB ρ).rank ≤ ρ.rank := by
  rw [← redA_swapM, ← rank_swapM ρ]
  exact rank_redA_le (isPPT_swapM h)

/-! ## Part 4. Rank two -/

theorem sub_kron {ι κ μ ν : Type*} (A B : Matrix ι κ ℂ) (C : Matrix μ ν ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext ⟨a, k⟩ ⟨b, l⟩
  simp [kroneckerMap_apply, sub_mul]

theorem kron_sub {ι κ μ ν : Type*} (A : Matrix ι κ ℂ) (B C : Matrix μ ν ℂ) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext ⟨a, k⟩ ⟨b, l⟩
  simp [kroneckerMap_apply, mul_sub]

/-- **Rank-two PPT states are separable** (P. Horodecki, Smolin, Terhal and Thapliyal 2003), in every
dimension: both reduced operators have rank at most two, so ρ lives on a 2 × 2 space. -/
theorem sep_of_rank_le_two {ρ : Mat n m} (h : IsPPT ρ) (hr : ρ.rank ≤ 2) : IsSeparable ρ := by
  obtain ⟨WA, hWA, hkerA, -⟩ := exists_support (isPSD_redA h.1)
  obtain ⟨WB, hWB, hkerB, -⟩ := exists_support (isPSD_redB h.1)
  have hsA : (redA ρ).rank ≤ 2 := (rank_redA_le h).trans hr
  have hsB : (redB ρ).rank ≤ 2 := (rank_redB_le h).trans hr
  have hH : ρᴴ = ρ := h.1.hermitian
  have hPA : (WA * WAᴴ)ᴴ = WA * WAᴴ := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hPB : (WB * WBᴴ)ᴴ = WB * WBᴴ := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have h1 : ρ * ((WA * WAᴴ) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) = ρ := by
    have := mul_kron_one_eq_zero h.1 hkerA
    rw [sub_kron, one_kronecker_one, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have h2 : ρ * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ (WB * WBᴴ)) = ρ := by
    have := mul_one_kron_eq_zero h.1 hkerB
    rw [kron_sub, one_kronecker_one, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have h3 : ρ * ((WA * WAᴴ) ⊗ₖ (WB * WBᴴ)) = ρ := by
    rw [show (WA * WAᴴ) ⊗ₖ (WB * WBᴴ) = ((WA * WAᴴ) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *
        ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ (WB * WBᴴ)) by
      rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul], ← Matrix.mul_assoc, h1, h2]
  have h4 : ((WA * WAᴴ) ⊗ₖ (WB * WBᴴ)) * ρ = ρ := by
    have := congrArg conjTranspose h3
    rwa [conjTranspose_mul, conjTranspose_kronecker, hPA, hPB, hH] at this
  set σ := lop WAᴴ WBᴴ ρ with hσdef
  have hback : lop WA WB σ = ρ := by
    rw [hσdef, lop_lop, lop, conjTranspose_kronecker, hPA, hPB, h4, h3]
  have hσ : IsPPT σ := isPPT_lop _ _ h
  have hτ : IsSeparable (lop (inclN _ 2) (inclN _ 2) σ) := pptSeparable22 _ (isPPT_lop _ _ hσ)
  have hσ' : lop (inclN _ 2)ᴴ (inclN _ 2)ᴴ (lop (inclN _ 2) (inclN _ 2) σ) = σ := by
    rw [lop_lop, inclN_conjTranspose_mul hsA, inclN_conjTranspose_mul hsB, lop_one]
  rw [← hback, ← hσ']
  exact isSeparable_lop _ _ (isSeparable_lop _ _ hτ)

/-! ### The PPT hypothesis is needed -/

/-- The Bell vector `|00⟩ + |11⟩`. -/
def bellVec : Idx 2 2 → ℂ := fun z => if z.1 = z.2 then 1 else 0

/-- The Bell state `|Φ⟩⟨Φ|`. -/
def bell : Mat 2 2 := vecMulVec bellVec (star bellVec)

theorem redA_bell : redA bell = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [redA, bell, bellVec, vecMulVec_apply]

/-- **The rank inequality fails without PPT**: the Bell state has rank one and `ρ_A = 1` of rank two, so
it is not PPT, and therefore (Peres) not separable. -/
theorem bell_not_ppt : ¬ IsPPT bell ∧ ¬ IsSeparable bell := by
  have hnot : ¬ IsPPT bell := fun h => by
    have h1 := rank_redA_le h
    rw [redA_bell, Matrix.rank_one, Fintype.card_fin] at h1
    have h2 := rank_vecMulVec_le bellVec (star bellVec)
    exact absurd (h1.trans h2) (by norm_num)
  exact ⟨hnot, fun hs => hnot (isPPT_of_isSeparable hs)⟩

end ChainReduction

end

end -- public section

#print axioms ChainReduction.reduction_identity
#print axioms ChainReduction.reduction_criterion
#print axioms ChainReduction.le_rank_of_reduction
#print axioms ChainReduction.exists_support
#print axioms ChainReduction.rank_redA_le
#print axioms ChainReduction.rank_redB_le
#print axioms ChainReduction.sep_of_rank_le_two
#print axioms ChainReduction.bell_not_ppt

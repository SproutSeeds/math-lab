module

/-
LocalUnitary.lean

The symmetry group of one link, and the selection of the (2, 3) link with no hypothesis left.

A link of type (f, c) joins a qudit of dimension f to one of dimension c. Its local basis changes are the
unitaries A ⊗ B on ℂ^f ⊗ ℂ^c. Chain Theory reads the gauge group off the qubit–qutrit link; this file makes
that reading exact.

  Part 1  `kronecker_eq_one_iff`: A ⊗ B = 1 exactly when A = a • 1 and B = a⁻¹ • 1 for some a ≠ 0.
  Part 2  The special product S(U(f) × U(c)), the pairs with det A · det B = 1, maps to the local-unitary
          group LU(f, c) = {A ⊗ B} by (A, B) ↦ A ⊗ B.
          `sHom_injective_iff`: the map is injective exactly when f and c differ by one.
          `sHom_range`: when f and c differ by one it is onto, so `luEquiv : S(U(f) × U(c)) ≃* LU(f, c)`.
  Part 3  `selection`: the alpha Letter's selection under the read cap (`selection_under_read_cap` in
          ChainAlpha.lean), with the cap proved (`ChainWoronowicz.readcap`): a readable type with an acting
          central charge (d₁ ≠ d₂) is (2, 3) or (3, 2).
          `readable_faithful_iff`: (2, 3) and (3, 2) are exactly the readable types whose special product
          acts faithfully on the link.

For (2, 3), S(U(2) × U(3)) is the Standard Model gauge group in its global form, (SU(3) × SU(2) × U(1))/ℤ₆
(Baez and Huerta, Bull. AMS 47 (2010) 483); GaugeGroup.lean proves that isomorphism (`gaugeEquiv`).
-/
public import MathLab.ChainTheory.Woronowicz
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

open Matrix
open scoped Kronecker

noncomputable section

namespace ChainLocalUnitary

/-! ## Part 1. When a Kronecker product is the identity -/

/-- **A ⊗ B = 1 exactly when A and B are inverse scalars.** -/
theorem kronecker_eq_one_iff {f c : ℕ} [NeZero f] [NeZero c] (A : Matrix (Fin f) (Fin f) ℂ)
    (B : Matrix (Fin c) (Fin c) ℂ) : A ⊗ₖ B = 1 ↔ ∃ a : ℂ, a ≠ 0 ∧ A = a • 1 ∧ B = a⁻¹ • 1 := by
  constructor
  · intro h
    have e : ∀ i j k l, A i j * B k l = (1 : Matrix (Fin f × Fin c) (Fin f × Fin c) ℂ) (i, k) (j, l) :=
      fun i j k l => by rw [← h, kroneckerMap_apply]
    have dd : ∀ i k, A i i * B k k = 1 := fun i k => by rw [e, one_apply_eq]
    have hB : ∀ k, B k k ≠ 0 := fun k hk => by simpa [hk] using dd 0 k
    have hA : ∀ i, A i i ≠ 0 := fun i hi => by simpa [hi] using dd i 0
    refine ⟨A 0 0, hA 0, ?_, ?_⟩
    · ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
        exact mul_right_cancel₀ (hB 0) ((dd i 0).trans (dd 0 0).symm)
      · have h0 := e i j 0 0
        rw [one_apply_ne (fun h => hij (congrArg Prod.fst h))] at h0
        rw [Matrix.smul_apply, one_apply_ne hij, smul_zero]
        exact (mul_eq_zero.1 h0).resolve_right (hB 0)
    · ext k l
      by_cases hkl : k = l
      · subst hkl
        rw [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
        exact eq_inv_of_mul_eq_one_right (dd 0 k)
      · have h0 := e 0 0 k l
        rw [one_apply_ne (fun h => hkl (congrArg Prod.snd h))] at h0
        rw [Matrix.smul_apply, one_apply_ne hkl, smul_zero]
        exact (mul_eq_zero.1 h0).resolve_left (hA 0)
  · rintro ⟨a, ha, rfl, rfl⟩
    rw [smul_kronecker, kronecker_smul, one_kronecker_one, smul_smul, mul_inv_cancel₀ ha, one_smul]

/-! ## Part 2. The special product and the local-unitary group -/

/-- A scalar of modulus one times a unitary is unitary. -/
theorem smul_mem_unitaryGroup {n : ℕ} {z : ℂ} (hz : z * star z = 1) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ unitaryGroup (Fin n) ℂ) : z • A ∈ unitaryGroup (Fin n) ℂ := by
  rw [mem_unitaryGroup_iff] at hA ⊢
  rw [star_smul, smul_mul_smul_comm, hA, hz, one_smul]

/-- A Kronecker product of unitaries is unitary. -/
theorem kronecker_mem_unitaryGroup {f c : ℕ} {A : Matrix (Fin f) (Fin f) ℂ} {B : Matrix (Fin c) (Fin c) ℂ}
    (hA : A ∈ unitaryGroup (Fin f) ℂ) (hB : B ∈ unitaryGroup (Fin c) ℂ) :
    A ⊗ₖ B ∈ unitaryGroup (Fin f × Fin c) ℂ := by
  rw [mem_unitaryGroup_iff] at hA hB ⊢
  rw [star_eq_conjTranspose, conjTranspose_kronecker, ← mul_kronecker_mul, ← star_eq_conjTranspose,
    ← star_eq_conjTranspose, hA, hB, one_kronecker_one]

/-- The local-unitary map of a link, (A, B) ↦ A ⊗ B. -/
def kronHom (f c : ℕ) :
    unitaryGroup (Fin f) ℂ × unitaryGroup (Fin c) ℂ →* unitaryGroup (Fin f × Fin c) ℂ where
  toFun p := ⟨(p.1 : Matrix (Fin f) (Fin f) ℂ) ⊗ₖ (p.2 : Matrix (Fin c) (Fin c) ℂ),
    kronecker_mem_unitaryGroup p.1.2 p.2.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' p q := Subtype.ext (by simp [mul_kronecker_mul])

/-- The local-unitary group of a link of type (f, c): the unitaries A ⊗ B on ℂ^f ⊗ ℂ^c. -/
def LU (f c : ℕ) : Subgroup (unitaryGroup (Fin f × Fin c) ℂ) := (kronHom f c).range

/-- The determinant of a unitary has modulus one. -/
theorem det_mul_star {n : ℕ} (A : unitaryGroup (Fin n) ℂ) :
    (A : Matrix (Fin n) (Fin n) ℂ).det * star (A : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
  rw [← det_conjTranspose, ← star_eq_conjTranspose, ← det_mul, mem_unitaryGroup_iff.1 A.2, det_one]

/-- **The special product S(U(f) × U(c))**: pairs of unitaries with det A · det B = 1. -/
def sProd (f c : ℕ) : Subgroup (unitaryGroup (Fin f) ℂ × unitaryGroup (Fin c) ℂ) where
  carrier := {p | (p.1 : Matrix (Fin f) (Fin f) ℂ).det * (p.2 : Matrix (Fin c) (Fin c) ℂ).det = 1}
  one_mem' := by simp
  mul_mem' {p q} hp hq := by
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, Submonoid.coe_mul, det_mul] at hp hq ⊢
    calc _ = ((p.1 : Matrix (Fin f) (Fin f) ℂ).det * (p.2 : Matrix (Fin c) (Fin c) ℂ).det) *
          ((q.1 : Matrix (Fin f) (Fin f) ℂ).det * (q.2 : Matrix (Fin c) (Fin c) ℂ).det) := by ring
      _ = 1 := by rw [hp, hq, one_mul]
  inv_mem' {p} hp := by
    simp only [Set.mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv] at hp ⊢
    have h1 : ((p.1⁻¹ : unitaryGroup (Fin f) ℂ) : Matrix (Fin f) (Fin f) ℂ) = star (p.1 : Matrix _ _ ℂ) := rfl
    have h2 : ((p.2⁻¹ : unitaryGroup (Fin c) ℂ) : Matrix (Fin c) (Fin c) ℂ) = star (p.2 : Matrix _ _ ℂ) := rfl
    rw [h1, h2, star_eq_conjTranspose, star_eq_conjTranspose, det_conjTranspose, det_conjTranspose,
      ← star_mul', hp, star_one]

/-- The special product acting on the link. -/
def sHom (f c : ℕ) : sProd f c →* unitaryGroup (Fin f × Fin c) ℂ := (kronHom f c).comp (sProd f c).subtype

theorem sHom_apply {f c : ℕ} (p : sProd f c) :
    (sHom f c p : Matrix (Fin f × Fin c) (Fin f × Fin c) ℂ) =
      ((p.1.1 : Matrix (Fin f) (Fin f) ℂ)) ⊗ₖ ((p.1.2 : Matrix (Fin c) (Fin c) ℂ)) := rfl

/-- The determinant of a scalar matrix. -/
theorem det_smul_one (n : ℕ) (z : ℂ) : (z • (1 : Matrix (Fin n) (Fin n) ℂ)).det = z ^ n := by
  rw [det_smul, det_one, mul_one, Fintype.card_fin]

/-- A scalar `z` with `z ^ f (z⁻¹) ^ c = 1` and modulus one gives the element (z • 1, z⁻¹ • 1) of the
special product; it acts on the link as the identity. -/
def scalarPair {f c : ℕ} (z : ℂ) (hz : z * star z = 1) (hpow : z ^ f * z⁻¹ ^ c = 1) : sProd f c :=
  have hzi : z⁻¹ * star z⁻¹ = 1 := by rw [star_inv₀, ← mul_inv, hz, inv_one]
  ⟨(⟨z • 1, smul_mem_unitaryGroup hz (one_mem _)⟩, ⟨z⁻¹ • 1, smul_mem_unitaryGroup hzi (one_mem _)⟩), by
    show (z • (1 : Matrix (Fin f) (Fin f) ℂ)).det * (z⁻¹ • (1 : Matrix (Fin c) (Fin c) ℂ)).det = 1
    rw [det_smul_one, det_smul_one, hpow]⟩

theorem pow_succ_mul_inv_pow {a : ℂ} (ha : a ≠ 0) (n : ℕ) : a ^ (n + 1) * a⁻¹ ^ n = a := by
  rw [pow_succ, inv_pow, mul_right_comm, mul_inv_cancel₀ (pow_ne_zero _ ha), one_mul]

theorem pow_mul_inv_pow_succ {a : ℂ} (ha : a ≠ 0) (n : ℕ) : a ^ n * a⁻¹ ^ (n + 1) = a⁻¹ := by
  rw [pow_succ, inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha), one_mul]

/-- When f and c differ by one, a scalar of modulus one corrects any determinant of modulus one. -/
theorem exists_scalar {f c : ℕ} (h : f = c + 1 ∨ c = f + 1) {δ : ℂ} (hδ : δ * star δ = 1) :
    ∃ z : ℂ, z * star z = 1 ∧ z ^ f * z⁻¹ ^ c * δ = 1 := by
  have hδ0 : δ ≠ 0 := fun h0 => by simp [h0] at hδ
  rcases h with rfl | rfl
  · refine ⟨star δ, by rw [star_star, mul_comm, hδ], ?_⟩
    rw [pow_succ_mul_inv_pow (star_ne_zero.2 hδ0), mul_comm, hδ]
  · refine ⟨δ, hδ, ?_⟩
    rw [pow_mul_inv_pow_succ hδ0, inv_mul_cancel₀ hδ0]

/-- **The special product acts faithfully on a link exactly when its two ends differ by one in
dimension.** -/
theorem sHom_injective_iff {f c : ℕ} [NeZero f] [NeZero c] :
    Function.Injective (sHom f c) ↔ (f = c + 1 ∨ c = f + 1) := by
  constructor
  · intro hinj
    by_contra hne
    push Not at hne
    -- a nontrivial scalar pair in the kernel
    obtain ⟨z, hz1, hz, hpow⟩ : ∃ z : ℂ, z ≠ 1 ∧ z * star z = 1 ∧ z ^ f * z⁻¹ ^ c = 1 := by
      rcases (by omega : f = c ∨ c + 2 ≤ f ∨ f + 2 ≤ c) with hfc | hfc | hfc
      · refine ⟨-1, by norm_num, by simp, ?_⟩
        subst hfc
        rw [inv_neg, inv_one, ← mul_pow, neg_one_mul, neg_neg, one_pow]
      · obtain ⟨k, rfl⟩ : ∃ k, f = c + k := ⟨f - c, by omega⟩
        have hk : 1 < k := by omega
        have hp := Complex.isPrimitiveRoot_exp k (by omega)
        set ζ := Complex.exp (2 * Real.pi * Complex.I / k)
        have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
        have hn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hp.pow_eq_one (by omega)
        refine ⟨ζ, hp.ne_one hk, ?_, ?_⟩
        · rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
        · rw [pow_add, mul_right_comm, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hζ0), one_mul, hp.pow_eq_one]
      · obtain ⟨k, rfl⟩ : ∃ k, c = f + k := ⟨c - f, by omega⟩
        have hk : 1 < k := by omega
        have hp := Complex.isPrimitiveRoot_exp k (by omega)
        set ζ := Complex.exp (2 * Real.pi * Complex.I / k)
        have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
        have hn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hp.pow_eq_one (by omega)
        refine ⟨ζ, hp.ne_one hk, ?_, ?_⟩
        · rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
        · rw [pow_add, inv_pow, inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hζ0), one_mul,
            hp.pow_eq_one, inv_one]
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz
    have hmap : sHom f c (scalarPair z hz hpow) = sHom f c 1 := by
      apply Subtype.ext
      rw [sHom_apply, map_one]
      exact (kronecker_eq_one_iff _ _).2 ⟨z, hz0, rfl, rfl⟩
    have h1 := congrArg (fun p : sProd f c => ((p.1.1 : Matrix (Fin f) (Fin f) ℂ)) 0 0) (hinj hmap)
    simp only [scalarPair] at h1
    exact hz1 (by simpa using h1)
  · intro h
    rw [injective_iff_map_eq_one]
    intro p hp
    have hk : ((p.1.1 : Matrix (Fin f) (Fin f) ℂ)) ⊗ₖ ((p.1.2 : Matrix (Fin c) (Fin c) ℂ)) = 1 := by
      rw [← sHom_apply, hp]; rfl
    obtain ⟨a, ha, hA, hB⟩ := (kronecker_eq_one_iff _ _).1 hk
    have hdet := p.2
    change ((p.1.1 : Matrix (Fin f) (Fin f) ℂ)).det * ((p.1.2 : Matrix (Fin c) (Fin c) ℂ)).det = 1 at hdet
    rw [hA, hB, det_smul_one, det_smul_one] at hdet
    have ha1 : a = 1 := by
      rcases h with rfl | rfl
      · rwa [pow_succ_mul_inv_pow ha] at hdet
      · rw [pow_mul_inv_pow_succ ha] at hdet
        exact inv_eq_one.1 hdet
    subst ha1
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext; simpa using hA
    · apply Subtype.ext; simpa using hB

/-- **When the ends differ by one, the special product is onto the local-unitary group.** -/
theorem sHom_range {f c : ℕ} (h : f = c + 1 ∨ c = f + 1) : (sHom f c).range = LU f c := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    exact ⟨p.1, rfl⟩
  · rintro _ ⟨⟨A, B⟩, rfl⟩
    have hδu : ((A : Matrix (Fin f) (Fin f) ℂ).det * (B : Matrix (Fin c) (Fin c) ℂ).det) *
        star ((A : Matrix (Fin f) (Fin f) ℂ).det * (B : Matrix (Fin c) (Fin c) ℂ).det) = 1 := by
      rw [star_mul', mul_mul_mul_comm, det_mul_star A, det_mul_star B, one_mul]
    obtain ⟨z, hz, hzdet⟩ := exists_scalar h hδu
    have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
    have hzi : z⁻¹ * star z⁻¹ = 1 := by rw [star_inv₀, ← mul_inv, hz, inv_one]
    let A' : unitaryGroup (Fin f) ℂ := ⟨z • (A : Matrix (Fin f) (Fin f) ℂ), smul_mem_unitaryGroup hz A.2⟩
    let B' : unitaryGroup (Fin c) ℂ := ⟨z⁻¹ • (B : Matrix (Fin c) (Fin c) ℂ), smul_mem_unitaryGroup hzi B.2⟩
    have hmem : (A', B') ∈ sProd f c := by
      show (z • (A : Matrix (Fin f) (Fin f) ℂ)).det * (z⁻¹ • (B : Matrix (Fin c) (Fin c) ℂ)).det = 1
      rw [det_smul, det_smul, Fintype.card_fin, Fintype.card_fin, mul_mul_mul_comm, hzdet]
    refine ⟨⟨(A', B'), hmem⟩, Subtype.ext ?_⟩
    rw [sHom_apply]
    show (z • (A : Matrix (Fin f) (Fin f) ℂ)) ⊗ₖ (z⁻¹ • (B : Matrix (Fin c) (Fin c) ℂ)) =
      (A : Matrix (Fin f) (Fin f) ℂ) ⊗ₖ (B : Matrix (Fin c) (Fin c) ℂ)
    rw [smul_kronecker, kronecker_smul, smul_smul, mul_inv_cancel₀ hz0, one_smul]

/-- **The local-unitary group of a link whose ends differ by one is the special product**:
LU(f, c) ≅ S(U(f) × U(c)). For the qubit–qutrit link this is S(U(2) × U(3)). -/
def luEquiv {f c : ℕ} [NeZero f] [NeZero c] (h : f = c + 1 ∨ c = f + 1) : sProd f c ≃* LU f c :=
  (MonoidHom.ofInjective (sHom_injective_iff.2 h)).trans (MulEquiv.subgroupCongr (sHom_range h))

/-! ## Part 3. The selection of the (2, 3) link -/

open ChoiDark ChainReadCap

/-- Readable types (d₁, d₂ ≥ 2) have both ends of dimension at most three. -/
theorem le_three_of_readable {d₁ d₂ : ℕ} (h₁ : 2 ≤ d₁) (h₂ : 2 ≤ d₂) (hr : Readable d₁ d₂) :
    d₁ ≤ 3 ∧ d₂ ≤ 3 := by
  have h6 : d₁ * d₂ ≤ 6 := (ChainWoronowicz.readcap d₁ d₂ h₁ h₂).1 hr
  constructor <;> nlinarith

/-- **The alpha Letter's selection, with no hypothesis**: a readable type with an acting central charge,
which acts on the link as the scalar i(d₂ − d₁) and so means d₁ ≠ d₂, is (2, 3) or (3, 2). This is
`selection_under_read_cap` of ChainAlpha.lean with the read cap proved. -/
theorem selection {d₁ d₂ : ℕ} (h₁ : 2 ≤ d₁) (h₂ : 2 ≤ d₂) (hr : Readable d₁ d₂) (hq : d₁ ≠ d₂) :
    (d₁ = 2 ∧ d₂ = 3) ∨ (d₁ = 3 ∧ d₂ = 2) := by
  obtain ⟨a₁, a₂⟩ := le_three_of_readable h₁ h₂ hr
  omega

/-- **(2, 3) and (3, 2) are exactly the readable link types on which the special product
S(U(d₁) × U(d₂)) acts faithfully**, so that their local-unitary group is S(U(2) × U(3)), the Standard
Model gauge group in its global form. -/
theorem readable_faithful_iff {d₁ d₂ : ℕ} (h₁ : 2 ≤ d₁) (h₂ : 2 ≤ d₂) :
    Readable d₁ d₂ ∧ Function.Injective (sHom d₁ d₂) ↔ (d₁ = 2 ∧ d₂ = 3) ∨ (d₁ = 3 ∧ d₂ = 2) := by
  have : NeZero d₁ := ⟨by omega⟩
  have : NeZero d₂ := ⟨by omega⟩
  rw [sHom_injective_iff]
  constructor
  · rintro ⟨hr, hd⟩
    obtain ⟨a₁, a₂⟩ := le_three_of_readable h₁ h₂ hr
    omega
  · intro h
    refine ⟨(ChainWoronowicz.readcap d₁ d₂ h₁ h₂).2 (by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num), ?_⟩
    omega

/-- Regression guard: the qubit–qutrit link is faithful, and the qubit–qubit link is not (its special
product contains (−1, −1), which acts as the identity). -/
theorem faithful_two_three : Function.Injective (sHom 2 3) := sHom_injective_iff.2 (Or.inr rfl)

theorem not_faithful_two_two : ¬ Function.Injective (sHom 2 2) := fun h => by
  have := sHom_injective_iff.1 h
  omega

end ChainLocalUnitary

end -- public section

#print axioms ChainLocalUnitary.kronecker_eq_one_iff
#print axioms ChainLocalUnitary.det_mul_star
#print axioms ChainLocalUnitary.sHom_injective_iff
#print axioms ChainLocalUnitary.exists_scalar
#print axioms ChainLocalUnitary.sHom_range
#print axioms ChainLocalUnitary.le_three_of_readable
#print axioms ChainLocalUnitary.selection
#print axioms ChainLocalUnitary.readable_faithful_iff
#print axioms ChainLocalUnitary.faithful_two_three
#print axioms ChainLocalUnitary.not_faithful_two_two

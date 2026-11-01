module

/-
GaugeGroup.lean

The local-unitary group of the qubit–qutrit link is the Standard Model gauge group in its global form.

LocalUnitary.lean shows LU(2, 3) ≅ S(U(2) × U(3)) (`ChainLocalUnitary.luEquiv`). This file adds the classical
covering of S(U(2) × U(3)) by SU(3) × SU(2) × U(1),

  (g, h, z) ↦ (z³ h, z⁻² g),

the hypercharge generator 6Y = diag(3, 3; −2, −2, −2) exponentiated (Baez and Huerta, Bull. AMS 47 (2010)
483). It proves:

  `smHom_surjective`  the map is onto S(U(2) × U(3));
  `mem_ker_smHom`     its kernel is {(z² • 1, z̄³ • 1, z) : z⁶ = 1};
  `kerEquiv`          the kernel is isomorphic to the sixth roots of unity, so it is cyclic of order six
                      (`card_ker`, `isCyclic_ker`): ℤ₆;
  `gaugeEquiv`        (SU(3) × SU(2) × U(1)) ⧸ ℤ₆ ≃* LU(2, 3), the local-unitary group of the qubit–qutrit link.
-/
public import MathLab.ChainTheory.LocalUnitary

@[expose] public section

open Matrix
open scoped Kronecker

noncomputable section

namespace ChainGaugeGroup

open ChainLocalUnitary

/-- SU(n) as unitary matrices of determinant one. -/
abbrev SU (n : ℕ) := specialUnitaryGroup (Fin n) ℂ

/-- U(1) as the unitary complex numbers. -/
abbrev U1 := unitary ℂ

theorem unit_mul_star (w : U1) : (w : ℂ) * star (w : ℂ) = 1 := Unitary.mul_star_self_of_mem w.2

theorem pow_mul_star_pow {w : ℂ} (hw : w * star w = 1) (n : ℕ) : w ^ n * star (w ^ n) = 1 := by
  rw [star_pow, ← mul_pow, hw, one_pow]

theorem star_mul_star_star {w : ℂ} (hw : w * star w = 1) : star w * star (star w) = 1 := by
  rw [star_star, mul_comm, hw]

theorem unitary_of_special {n : ℕ} (A : SU n) : (A : Matrix (Fin n) (Fin n) ℂ) ∈ unitaryGroup (Fin n) ℂ :=
  (mem_specialUnitaryGroup_iff.1 A.2).1

theorem det_special {n : ℕ} (A : SU n) : (A : Matrix (Fin n) (Fin n) ℂ).det = 1 :=
  (mem_specialUnitaryGroup_iff.1 A.2).2

/-- The image of (g, h, z): the pair (z³ h, z̄² g) of unitaries. -/
def smPair (x : SU 3 × SU 2 × U1) : unitaryGroup (Fin 2) ℂ × unitaryGroup (Fin 3) ℂ :=
  (⟨((x.2.2 : ℂ) ^ 3) • (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ),
      smul_mem_unitaryGroup (pow_mul_star_pow (unit_mul_star x.2.2) 3) (unitary_of_special x.2.1)⟩,
    ⟨(star (x.2.2 : ℂ) ^ 2) • (x.1 : Matrix (Fin 3) (Fin 3) ℂ),
      smul_mem_unitaryGroup (pow_mul_star_pow (star_mul_star_star (unit_mul_star x.2.2)) 2)
        (unitary_of_special x.1)⟩)

theorem smPair_mem (x : SU 3 × SU 2 × U1) : smPair x ∈ sProd 2 3 := by
  show ((((x.2.2 : ℂ) ^ 3) • (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ)).det *
    ((star (x.2.2 : ℂ) ^ 2) • (x.1 : Matrix (Fin 3) (Fin 3) ℂ)).det) = 1
  rw [det_smul, det_smul, det_special, det_special, Fintype.card_fin, Fintype.card_fin, mul_one, mul_one,
    ← pow_mul, ← pow_mul]
  show (x.2.2 : ℂ) ^ 6 * star (x.2.2 : ℂ) ^ 6 = 1
  rw [← mul_pow, unit_mul_star, one_pow]

theorem norm_eq_one_of_mul_star {z : ℂ} (h : z * star z = 1) : ‖z‖ = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have h2 : ‖z‖ ^ 2 = 1 := by exact_mod_cast h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by norm_num)).1 h2

theorem mul_star_of_norm_eq_one {z : ℂ} (h : ‖z‖ = 1) : z * star z = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; norm_num

/-- A complex number of modulus one as an element of U(1). -/
def toU1 (w : ℂ) (hw : w * star w = 1) : U1 :=
  ⟨w, Unitary.mem_iff.2 ⟨by rw [mul_comm]; exact hw, hw⟩⟩

/-- A scalar matrix of modulus one and determinant one as an element of SU(n). -/
def scalarSU (n : ℕ) (w : ℂ) (hw : w * star w = 1) (hdet : w ^ n = 1) : SU n :=
  ⟨w • 1, mem_specialUnitaryGroup_iff.2 ⟨smul_mem_unitaryGroup hw (one_mem _), by
    rw [det_smul, det_one, mul_one, Fintype.card_fin, hdet]⟩⟩

/-- **The Standard Model covering** SU(3) × SU(2) × U(1) → S(U(2) × U(3)), (g, h, z) ↦ (z³ h, z̄² g). -/
def smHom : SU 3 × SU 2 × U1 →* sProd 2 3 where
  toFun x := ⟨smPair x, smPair_mem x⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> simp [smPair]
  map_mul' x y := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · show ((x.2.2 * y.2.2 : U1) : ℂ) ^ 3 • ((x.2.1 * y.2.1 : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) =
        ((x.2.2 : ℂ) ^ 3 • (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((y.2.2 : ℂ) ^ 3 • (y.2.1 : Matrix (Fin 2) (Fin 2) ℂ))
      simp only [Submonoid.coe_mul]
      rw [smul_mul_smul_comm, mul_pow]
    · show star ((x.2.2 * y.2.2 : U1) : ℂ) ^ 2 • ((x.1 * y.1 : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) =
        (star (x.2.2 : ℂ) ^ 2 • (x.1 : Matrix (Fin 3) (Fin 3) ℂ)) * (star (y.2.2 : ℂ) ^ 2 • (y.1 : Matrix (Fin 3) (Fin 3) ℂ))
      simp only [Submonoid.coe_mul]
      rw [smul_mul_smul_comm, star_mul', mul_pow]

theorem smHom_fst (x : SU 3 × SU 2 × U1) :
    (((smHom x).1.1 : unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (x.2.2 : ℂ) ^ 3 • (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem smHom_snd (x : SU 3 × SU 2 × U1) :
    (((smHom x).1.2 : unitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) =
      star (x.2.2 : ℂ) ^ 2 • (x.1 : Matrix (Fin 3) (Fin 3) ℂ) := rfl

/-- **The covering is onto S(U(2) × U(3)).** -/
theorem smHom_surjective : Function.Surjective smHom := by
  rintro ⟨⟨A, B⟩, hAB⟩
  have hAB' : (A : Matrix (Fin 2) (Fin 2) ℂ).det * (B : Matrix (Fin 3) (Fin 3) ℂ).det = 1 := hAB
  have ha := det_mul_star A
  obtain ⟨w, hw6⟩ := IsAlgClosed.exists_pow_nat_eq (A : Matrix (Fin 2) (Fin 2) ℂ).det (by norm_num : 0 < 6)
  have hw : w * star w = 1 := by
    apply mul_star_of_norm_eq_one
    have h1 : ‖w‖ ^ 6 = 1 := by rw [← norm_pow, hw6, norm_eq_one_of_mul_star ha]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) (by norm_num)).1 h1
  have hsw := star_mul_star_star hw
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw
  -- h = z̄³ A in SU(2) and g = z² B in SU(3)
  have hh : star w ^ 3 • (A : Matrix (Fin 2) (Fin 2) ℂ) ∈ specialUnitaryGroup (Fin 2) ℂ := by
    refine mem_specialUnitaryGroup_iff.2 ⟨smul_mem_unitaryGroup (pow_mul_star_pow hsw 3) A.2, ?_⟩
    rw [det_smul, Fintype.card_fin, ← pow_mul, ← hw6, ← mul_pow, mul_comm, hw, one_pow]
  have hg : w ^ 2 • (B : Matrix (Fin 3) (Fin 3) ℂ) ∈ specialUnitaryGroup (Fin 3) ℂ := by
    refine mem_specialUnitaryGroup_iff.2 ⟨smul_mem_unitaryGroup (pow_mul_star_pow hw 2) B.2, ?_⟩
    rw [det_smul, Fintype.card_fin, ← pow_mul, hw6, hAB']
  refine ⟨(⟨_, hg⟩, ⟨_, hh⟩, toU1 w hw), ?_⟩
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · show w ^ 3 • (star w ^ 3 • (A : Matrix (Fin 2) (Fin 2) ℂ)) = (A : Matrix (Fin 2) (Fin 2) ℂ)
    rw [smul_smul, ← mul_pow, hw, one_pow, one_smul]
  · show star w ^ 2 • (w ^ 2 • (B : Matrix (Fin 3) (Fin 3) ℂ)) = (B : Matrix (Fin 3) (Fin 3) ℂ)
    rw [smul_smul, ← mul_pow, mul_comm, hw, one_pow, one_smul]

/-- The sixth roots of unity, embedded in SU(3) × SU(2) × U(1) as ζ ↦ (ζ² • 1, ζ̄³ • 1, ζ). -/
def rootsHom : rootsOfUnity 6 ℂ →* SU 3 × SU 2 × U1 where
  toFun ζ :=
    have h6 : ((ζ : ℂˣ) : ℂ) ^ 6 = 1 := (mem_rootsOfUnity' 6 (ζ : ℂˣ)).1 ζ.2
    have hu : ((ζ : ℂˣ) : ℂ) * star ((ζ : ℂˣ) : ℂ) = 1 :=
      mul_star_of_norm_eq_one (Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num))
    (scalarSU 3 (((ζ : ℂˣ) : ℂ) ^ 2) (pow_mul_star_pow hu 2) (by rw [← pow_mul, h6]),
      scalarSU 2 (star ((ζ : ℂˣ) : ℂ) ^ 3) (pow_mul_star_pow (star_mul_star_star hu) 3)
        (by rw [← pow_mul, ← star_pow, h6, star_one]),
      toU1 _ hu)
  map_one' := by
    apply Prod.ext
    · apply Subtype.ext; simp [scalarSU]
    apply Prod.ext
    · apply Subtype.ext; simp [scalarSU]
    · apply Subtype.ext; simp [toU1]
  map_mul' ζ η := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [scalarSU, Prod.fst_mul, Submonoid.coe_mul, Subgroup.coe_mul, Units.val_mul, smul_mul_smul_comm,
        mul_one, mul_pow]
    apply Prod.ext
    · apply Subtype.ext
      simp only [scalarSU, Prod.snd_mul, Prod.fst_mul, Submonoid.coe_mul, Subgroup.coe_mul, Units.val_mul,
        smul_mul_smul_comm, mul_one, star_mul', mul_pow]
    · apply Subtype.ext
      rfl

theorem rootsHom_injective : Function.Injective rootsHom := by
  intro ζ η h
  have := congrArg (fun x : SU 3 × SU 2 × U1 => ((x.2.2 : U1) : ℂ)) h
  exact Subtype.ext (Units.ext this)

/-- **The kernel of the covering is the sixth roots of unity.** -/
theorem ker_smHom : smHom.ker = rootsHom.range := by
  ext x
  constructor
  · intro hx
    have h1 : smHom x = 1 := hx
    have hA := congrArg (fun p : sProd 2 3 => ((p.1.1 : unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) h1
    have hB := congrArg (fun p : sProd 2 3 => ((p.1.2 : unitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)) h1
    rw [smHom_fst] at hA
    rw [smHom_snd] at hB
    set w : ℂ := (x.2.2 : ℂ) with hwdef
    have hw : w * star w = 1 := unit_mul_star x.2.2
    have hsw := star_mul_star_star hw
    -- h = z̄³ • 1 and g = z² • 1
    have hh : (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = star w ^ 3 • 1 := by
      have := congrArg (fun M => star w ^ 3 • M) hA
      simp only [smul_smul, ← mul_pow] at this
      rw [mul_comm (star w) w, hw, one_pow, one_smul] at this
      simpa using this
    have hg : (x.1 : Matrix (Fin 3) (Fin 3) ℂ) = w ^ 2 • 1 := by
      have := congrArg (fun M => w ^ 2 • M) hB
      simp only [smul_smul, ← mul_pow] at this
      rw [hw, one_pow, one_smul] at this
      simpa using this
    have h6 : w ^ 6 = 1 := by
      have hd := det_special x.1
      rw [hg, det_smul, det_one, mul_one, Fintype.card_fin, ← pow_mul] at hd
      exact hd
    have hζ : (Units.mk0 w (fun h0 => by simp [h0] at hw)) ∈ rootsOfUnity 6 ℂ :=
      (mem_rootsOfUnity' 6 _).2 h6
    refine ⟨⟨_, hζ⟩, ?_⟩
    apply Prod.ext
    · apply Subtype.ext; exact hg.symm
    apply Prod.ext
    · apply Subtype.ext; exact hh.symm
    · apply Subtype.ext; rfl
  · rintro ⟨ζ, rfl⟩
    show smHom (rootsHom ζ) = 1
    have h6 : ((ζ : ℂˣ) : ℂ) ^ 6 = 1 := (mem_rootsOfUnity' 6 (ζ : ℂˣ)).1 ζ.2
    have hu : ((ζ : ℂˣ) : ℂ) * star ((ζ : ℂˣ) : ℂ) = 1 :=
      mul_star_of_norm_eq_one (Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num))
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · show ((ζ : ℂˣ) : ℂ) ^ 3 • (star ((ζ : ℂˣ) : ℂ) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1
      rw [smul_smul, ← mul_pow, hu, one_pow, one_smul]
    · show star ((ζ : ℂˣ) : ℂ) ^ 2 • (((ζ : ℂˣ) : ℂ) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ)) = 1
      rw [smul_smul, ← mul_pow, mul_comm, hu, one_pow, one_smul]

/-- The kernel of the covering is isomorphic to the sixth roots of unity. -/
noncomputable def kerEquiv : rootsOfUnity 6 ℂ ≃* smHom.ker :=
  (MonoidHom.ofInjective rootsHom_injective).trans (MulEquiv.subgroupCongr ker_smHom.symm)

/-- **The kernel has exactly six elements** … -/
theorem card_ker : Nat.card smHom.ker = 6 := by
  rw [← Nat.card_congr kerEquiv.toEquiv, Complex.card_rootsOfUnity]

/-- … **and is cyclic**: it is ℤ₆. -/
theorem isCyclic_ker : IsCyclic smHom.ker := isCyclic_of_surjective kerEquiv.toMonoidHom kerEquiv.surjective

/-- **(SU(3) × SU(2) × U(1)) ⧸ ℤ₆ ≅ S(U(2) × U(3))**, the global form of the Standard Model gauge group. -/
noncomputable def smEquiv : (SU 3 × SU 2 × U1) ⧸ smHom.ker ≃* sProd 2 3 :=
  QuotientGroup.quotientKerEquivOfSurjective smHom smHom_surjective

/-- **The local-unitary group of the qubit–qutrit link is the Standard Model gauge group**:
(SU(3) × SU(2) × U(1)) ⧸ ℤ₆ ≃* LU(2, 3), with the kernel cyclic of order six (`card_ker`, `isCyclic_ker`). -/
noncomputable def gaugeEquiv : (SU 3 × SU 2 × U1) ⧸ smHom.ker ≃* LU 2 3 :=
  smEquiv.trans (luEquiv (Or.inr rfl))

end ChainGaugeGroup

end -- public section

#print axioms ChainGaugeGroup.smPair_mem
#print axioms ChainGaugeGroup.smHom_surjective
#print axioms ChainGaugeGroup.rootsHom_injective
#print axioms ChainGaugeGroup.ker_smHom
#print axioms ChainGaugeGroup.card_ker
#print axioms ChainGaugeGroup.isCyclic_ker
#print axioms ChainGaugeGroup.smEquiv
#print axioms ChainGaugeGroup.gaugeEquiv

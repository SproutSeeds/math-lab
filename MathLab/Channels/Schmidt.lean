module

/-
Channels/Schmidt.lean

Schmidt number, and how a Schmidt-number bound proves PPT².

  `IsSchmidtLE k ρ`   ρ is a sum of rank-one projectors onto sums of at most `k` product vectors
                      (Schmidt number at most `k`). For `k = 1` this is separability.
  `isEB_comp_of_isSchmidtLE`  if the Choi matrix of Ψ has Schmidt number at most `k`, Φ is PPT, and PPT
                      operators on `ℂᵏ ⊗ ℂᵖ` are separable, then `Φ ∘ Ψ` is entanglement breaking.
  `pptSquared_three_of_schmidt`  PPT² on `M_3` follows from a Schmidt-number bound for PPT states on
                      `ℂ³ ⊗ ℂ³` (Yang, Leung and Tang 2016), with the 2 × 3 PPT criterion.
  `not_schmidt_route_four`  no Schmidt-number bound makes the same argument work on `M_4`.
-/
public import MathLab.Channels.Basic

@[expose] public section

open Matrix
open scoped Kronecker

noncomputable section

namespace Channels

open ChoiDark ChainDuality ChainStormer ChainWoronowicz ChainPPT ChainReduction ChainLowRankMN

variable {n m p k : ℕ}

/-- A sum of `k` product vectors `Σ_j α_j ⊗ β_j`, which has Schmidt rank at most `k`. -/
def schmidtVec (α : Fin k → Fin n → ℂ) (β : Fin k → Fin m → ℂ) : Idx n m → ℂ := ∑ j, prodVec (α j) (β j)

/-- **Schmidt number at most `k`**: a finite sum of rank-one projectors onto sums of at most `k` product
vectors. -/
def IsSchmidtLE (k : ℕ) (ρ : Mat n m) : Prop :=
  ∃ (t : ℕ) (α : Fin t → Fin k → Fin n → ℂ) (β : Fin t → Fin k → Fin m → ℂ),
    ρ = ∑ s, vecMulVec (schmidtVec (α s) (β s)) (star (schmidtVec (α s) (β s)))

/-- **Schmidt number one is separability.** -/
theorem isSchmidtLE_one_iff {ρ : Mat n m} : IsSchmidtLE 1 ρ ↔ IsSeparable ρ := by
  constructor
  · rintro ⟨t, α, β, rfl⟩
    exact ⟨t, fun s => α s 0, fun s => β s 0, by simp [schmidtVec]⟩
  · rintro ⟨t, x, y, rfl⟩
    exact ⟨t, fun s _ => x s, fun s _ => y s, by simp [schmidtVec]⟩

theorem eq_zero_of_isSchmidtLE_zero {ρ : Mat n m} (h : IsSchmidtLE 0 ρ) : ρ = 0 := by
  obtain ⟨t, α, β, rfl⟩ := h
  simp [schmidtVec]

/-- The factor `W : ℂᵏ → ℂⁿ` with columns `α_j`. -/
def schmidtFactor (α : Fin k → Fin n → ℂ) : Matrix (Fin n) (Fin k) ℂ := Matrix.of fun a j => α j a

/-- The coefficients `u = Σ_j e_j ⊗ β_j ∈ ℂᵏ ⊗ ℂᵐ`. -/
def schmidtCoeff (β : Fin k → Fin m → ℂ) : Idx k m → ℂ := fun z => β z.1 z.2

/-- **A sum of `k` product vectors lives on a `k`-dimensional first factor**: `Σ_j α_j ⊗ β_j = (W ⊗ 1) u`. -/
theorem schmidtVec_eq (α : Fin k → Fin n → ℂ) (β : Fin k → Fin m → ℂ) :
    schmidtVec α β = (schmidtFactor α ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ schmidtCoeff β := by
  ext ⟨a, l⟩
  simp [schmidtVec, schmidtFactor, schmidtCoeff, prodVec, mulVec, dotProduct, kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_apply]

theorem vecMulVec_schmidtVec (α : Fin k → Fin n → ℂ) (β : Fin k → Fin m → ℂ) :
    vecMulVec (schmidtVec α β) (star (schmidtVec α β)) =
      lop (schmidtFactor α) (1 : Matrix (Fin m) (Fin m) ℂ)
        (vecMulVec (schmidtCoeff β) (star (schmidtCoeff β))) := by
  rw [schmidtVec_eq, MathLab.vecMulVec_mulVec_star]
  rfl

/-- **A Schmidt-number bound and a PPT map give an entanglement breaking composition.** If the Choi matrix
of Ψ has Schmidt number at most `k`, Φ is PPT, and PPT operators on `ℂᵏ ⊗ ℂᵖ` are separable, then `Φ ∘ Ψ`
is entanglement breaking. Each pure part of `C(Ψ)` lives on `ℂᵏ ⊗ ℂᵐ`, and `id ⊗ Φ` takes it to a PPT
operator on `ℂᵏ ⊗ ℂᵖ`. -/
theorem isEB_comp_of_isSchmidtLE {Ψ : Lin n m} {Φ : Lin m p} (hΨ : IsSchmidtLE k (choi Ψ))
    (hΦ : IsPPTMap Φ) (hk : AllPPTSeparable k p) : IsEB (Φ ∘ₗ Ψ) := by
  obtain ⟨t, α, β, hαβ⟩ := hΨ
  rw [IsEB, choi_comp, hαβ, applyR_sum]
  refine isSeparable_sum _ _ fun s _ => ?_
  rw [vecMulVec_schmidtVec, applyR_lop_left]
  exact isSeparable_lop _ _ (hk _ (isPPT_applyR hΦ (isPSD_rank_one _)))

/-- **PPT² from a Schmidt-number bound**: if every PPT operator on `ℂᵈ ⊗ ℂᵈ` has Schmidt number at most
`k`, and PPT operators on `ℂᵏ ⊗ ℂᵈ` are separable, then PPT² holds on `M_d`. -/
theorem pptSquared_of_isSchmidtLE {d : ℕ} (hS : ∀ ρ : Mat d d, IsPPT ρ → IsSchmidtLE k ρ)
    (hk : AllPPTSeparable k d) : PPTSquared d :=
  fun _ _ hΦ hΨ => isEB_comp_of_isSchmidtLE (hS _ hΨ) hΦ hk

/-- **PPT² on `M_3` reduces to a Schmidt-number bound**: if every PPT operator on `ℂ³ ⊗ ℂ³` has Schmidt
number at most 2 (Yang, Leung and Tang 2016), then PPT² holds on `M_3`. The second hypothesis of
`pptSquared_of_isSchmidtLE` is the 2 × 3 PPT criterion. -/
theorem pptSquared_three_of_schmidt (hS : ∀ ρ : Mat 3 3, IsPPT ρ → IsSchmidtLE 2 ρ) : PPTSquared 3 :=
  pptSquared_of_isSchmidtLE hS pptSeparable23

/-- **The route stops at `M_4`**: no Schmidt-number bound `k` meets both hypotheses of
`pptSquared_of_isSchmidtLE` for `d = 4`. For `k ≤ 1` there are PPT entangled states on `ℂ⁴ ⊗ ℂ⁴`; for
`k ≥ 2` there are PPT entangled states on `ℂᵏ ⊗ ℂ⁴`, since `4k > 6`. -/
theorem not_schmidt_route_four (k : ℕ) :
    ¬ ((∀ ρ : Mat 4 4, IsPPT ρ → IsSchmidtLE k ρ) ∧ AllPPTSeparable k 4) := by
  rintro ⟨hS, hk⟩
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain ⟨ρ, hρ, hns⟩ := exists_ppt_entangled (d₁ := 4) (d₂ := 4) (by norm_num) (by norm_num) (by norm_num)
    have hρS := hS ρ hρ
    interval_cases k
    · exact hns (by rw [eq_zero_of_isSchmidtLE_zero hρS]; exact isSeparable_zero)
    · exact hns (isSchmidtLE_one_iff.1 hρS)
  · have := (ppt_criterion h (by norm_num : 2 ≤ 4)).1 hk
    omega

end Channels

end

end -- public section

#print axioms Channels.isSchmidtLE_one_iff
#print axioms Channels.isEB_comp_of_isSchmidtLE
#print axioms Channels.pptSquared_three_of_schmidt
#print axioms Channels.not_schmidt_route_four

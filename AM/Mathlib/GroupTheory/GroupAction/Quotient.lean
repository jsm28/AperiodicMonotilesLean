import Mathlib.GroupTheory.GroupAction.Quotient

variable {α : Type*} {β : Type*}

open Function

namespace MulAction

variable [Group α]

open QuotientGroup

variable [MulAction α β] (x : β)

local notation "Ω" => Quotient <| orbitRel α β

/-- Given a group acting freely and transitively, an equivalence between the orbits under the
action of a subgroup and the quotient group. -/
@[to_additive "Given an additive group acting freely and transitively, an equivalence between the
orbits under the action of an additive subgroup and the quotient group."]
noncomputable def equivSubgroupOrbitsQuotientGroup [IsPretransitive α β]
    (free : ∀ y : β, MulAction.stabilizer α y = ⊥) (H : Subgroup α) :
    orbitRel.Quotient H β ≃ α ⧸ H where
  toFun := fun q ↦ q.liftOn' (fun y ↦ (exists_smul_eq α y x).choose) (by
    intro y₁ y₂ h
    rw [orbitRel_r_apply] at h
    rw [Quotient.eq'', leftRel_eq]
    dsimp only
    rcases h with ⟨g, rfl⟩
    dsimp only
    suffices (exists_smul_eq α (g • y₂) x).choose = (exists_smul_eq α y₂ x).choose * g⁻¹ by
      simp [this]
    rw [← inv_mul_eq_one, ← Subgroup.mem_bot, ← free ((g : α) • y₂)]
    simp only [mem_stabilizer_iff, smul_smul, mul_assoc, InvMemClass.coe_inv, inv_mul_cancel,
               mul_one]
    rw [← smul_smul, (exists_smul_eq α y₂ x).choose_spec, inv_smul_eq_iff,
        (exists_smul_eq α ((g : α) • y₂) x).choose_spec])
  invFun := fun q ↦ q.liftOn' (fun g ↦ ⟦g⁻¹ • x⟧) (by
    intro g₁ g₂ h
    rw [leftRel_eq] at h
    simp only
    rw [← @Quotient.mk''_eq_mk, Quotient.eq'', orbitRel_r_apply]
    exact ⟨⟨_, h⟩, by simp [mul_smul]⟩)
  left_inv := fun y ↦ by
    induction' y using Quotient.inductionOn' with y
    simp only [Quotient.liftOn'_mk'']
    rw [← @Quotient.mk''_eq_mk, Quotient.eq'', orbitRel_r_apply]
    convert mem_orbit_self _
    rw [inv_smul_eq_iff, (exists_smul_eq α y x).choose_spec]
  right_inv := fun g ↦ by
    induction' g using Quotient.inductionOn' with g
    simp only [Quotient.liftOn'_mk'', Quotient.liftOn'_mk, QuotientGroup.mk]
    rw [Quotient.eq'', leftRel_eq]
    simp only
    convert one_mem H
    rw [inv_mul_eq_one, eq_comm, ← inv_mul_eq_one, ← Subgroup.mem_bot, ← free (g⁻¹ • x),
        mem_stabilizer_iff, mul_smul, (exists_smul_eq α (g⁻¹ • x) x).choose_spec]

end MulAction

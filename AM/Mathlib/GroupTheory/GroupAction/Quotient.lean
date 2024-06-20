import Mathlib.GroupTheory.GroupAction.Quotient

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Function

open BigOperators

namespace MulAction

variable [Group α]

open QuotientGroup

variable (α) [Group α] [MulAction α β] (x : β)

variable (β)

local notation "Ω" => Quotient <| orbitRel α β

variable {α β}

@[to_additive]
lemma finite_quotient_of_pretransitive_of_finite_quotient [IsPretransitive α β] {H : Subgroup α}
    (h : Finite (α ⧸ H)) : Finite <| orbitRel.Quotient H β := by
  rcases isEmpty_or_nonempty β with he | ⟨⟨b⟩⟩
  · exact Quotient.finite _
  · have h' : Finite (Quotient (rightRel H)) :=
      Finite.of_equiv _ (quotientRightRelEquivQuotientLeftRel _).symm
    let f : Quotient (rightRel H) → orbitRel.Quotient H β :=
      fun a ↦ Quotient.liftOn' a (fun g ↦ ⟦g • b⟧) fun g₁ g₂ r ↦ by
        replace r := Setoid.symm' _ r
        change @Setoid.r _ (rightRel H) _ _ at r
        rw [rightRel_eq] at r
        simp only [Quotient.eq]
        change g₁ • b ∈ orbit H (g₂ • b)
        rw [mem_orbit_iff]
        exact ⟨⟨g₁ * g₂⁻¹, r⟩, by simp [mul_smul]⟩
    exact Finite.of_surjective f ((Quotient.surjective_liftOn' _).2
      (Quotient.surjective_Quotient_mk''.comp (MulAction.surjective_smul _ _)))

/-- A bijection between the quotient of the action of a subgroup `H` on an orbit, and a
corresponding quotient expressed in terms of `Setoid.comap Subtype.val`. -/
@[to_additive "A bijection between the quotient of the action of an additive subgroup `H` on an
orbit, and a corresponding quotient expressed in terms of `Setoid.comap Subtype.val`."]
noncomputable def equivSubgroupOrbitsSetoidComap (H : Subgroup α) (ω : Ω) :
    orbitRel.Quotient H (orbitRel.Quotient.orbit ω) ≃
      Quotient ((orbitRel H β).comap (Subtype.val : Quotient.mk (orbitRel α β) ⁻¹' {ω} → β)) where
  toFun := fun q ↦ q.liftOn' (fun x ↦ ⟦⟨↑x, by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hx := x.property
    rwa [orbitRel.Quotient.mem_orbit, @Quotient.mk''_eq_mk] at hx⟩⟧) fun a b h ↦ by
      simp only [← Quotient.eq'', Quotient.mk''_eq_mk,
                 orbitRel.Quotient.subgroup_quotient_eq_iff] at h
      simp only [← Quotient.mk''_eq_mk, Quotient.eq''] at h ⊢
      exact h
  invFun := fun q ↦ q.liftOn' (fun x ↦ ⟦⟨↑x, by
    have hx := x.property
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    rwa [orbitRel.Quotient.mem_orbit, @Quotient.mk''_eq_mk]⟩⟧) fun a b h ↦ by
      change Setoid.Rel _ _ _ at h
      rw [Setoid.comap_rel, Setoid.Rel, ← Quotient.eq'', @Quotient.mk''_eq_mk] at h
      simp only [orbitRel.Quotient.subgroup_quotient_eq_iff]
      exact h
  left_inv := by
    simp only [LeftInverse]
    intro q
    induction q using Quotient.inductionOn'
    rfl
  right_inv := by
    simp only [Function.RightInverse, LeftInverse]
    intro q
    induction q using Quotient.inductionOn'
    rfl

variable (β)

/-- A bijection between the orbits under the action of a subgroup `H` on `β`, and the orbits
under the action of `H` on each orbit under the action of `G`. -/
@[to_additive "A bijection between the orbits under the action of an additive subgroup `H` on `β`,
and the orbits under the action of `H` on each orbit under the action of `G`."]
noncomputable def equivSubgroupOrbits (H : Subgroup α) :
    orbitRel.Quotient H β ≃ Σω : Ω, orbitRel.Quotient H (orbitRel.Quotient.orbit ω) := by
  calc
    orbitRel.Quotient H β ≃ Σω : Ω, Quotient ((orbitRel H β).comap
      (Subtype.val : Quotient.mk (orbitRel α β) ⁻¹' {ω} → β)) :=
        (Setoid.sigmaQuotientEquivOfLe (orbitRel_subgroup_le H)).symm
    _ ≃ Σω : Ω, orbitRel.Quotient H (orbitRel.Quotient.orbit ω) :=
      Equiv.sigmaCongrRight fun ω ↦ (equivSubgroupOrbitsSetoidComap H ω).symm

variable {β}

@[to_additive]
lemma finite_quotient_of_finite_quotient_of_finite_quotient {H : Subgroup α}
    (hb : Finite (orbitRel.Quotient α β)) (h : Finite (α ⧸ H)) :
    Finite <| orbitRel.Quotient H β := by
  rw [(equivSubgroupOrbits β H).finite_iff]
  have h' : ∀ ω : orbitRel.Quotient α β,
      Finite (orbitRel.Quotient H (orbitRel.Quotient.orbit ω)) := by
    intro ω
    exact finite_quotient_of_pretransitive_of_finite_quotient h
  infer_instance

end MulAction

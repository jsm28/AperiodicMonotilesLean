import Mathlib.Data.Setoid.Basic

variable {α : Type*} {β : Type*}

namespace Setoid

lemma prod_apply {r : Setoid α} {s : Setoid β} {x₁ x₂ : α} {y₁ y₂ : β} :
    @Setoid.r _ (r.prod s) (x₁, y₁) (x₂, y₂) ↔ (@Setoid.r _ r x₁ x₂ ∧ @Setoid.r _ s y₁ y₂) :=
  Iff.rfl

lemma piSetoid_apply {ι : Sort*} {α : ι → Sort*} {r : ∀ i, Setoid (α i)} {x y : ∀ i, α i} :
    @Setoid.r _ (@piSetoid _ _ r) x y ↔ ∀ i, @Setoid.r _ (r i) (x i) (y i) :=
  Iff.rfl

/-- A bijection between the product of two quotients and the quotient by the product of the
equivalence relations. -/
def prodQuotientEquiv (r : Setoid α) (s : Setoid β) :
    Quotient r × Quotient s ≃ Quotient (r.prod s) where
  toFun := fun (x, y) ↦ Quotient.map₂' Prod.mk (fun _ _ hx _ _ hy ↦ ⟨hx, hy⟩) x y
  invFun := fun q ↦ Quotient.liftOn' q (fun xy ↦ (Quotient.mk'' xy.1, Quotient.mk'' xy.2))
    fun x y hxy ↦ Prod.ext (by simpa using hxy.1) (by simpa using hxy.2)
  left_inv := fun q ↦ by
    rcases q with ⟨qa, qb⟩
    exact Quotient.inductionOn₂' qa qb fun _ _ ↦ rfl
  right_inv := fun q ↦ by
    simp only
    refine Quotient.inductionOn' q fun _ ↦ rfl

/-- A bijection between an indexed product of quotients and the quotient by the product of the
equivalence relations. -/
noncomputable def piQuotientEquiv {ι : Sort*} {α : ι → Sort*} (r : ∀ i, Setoid (α i)) :
    (∀ i, Quotient (r i)) ≃ Quotient (@piSetoid _ _ r) where
  toFun := fun x ↦ Quotient.mk'' fun i ↦ (x i).out'
  invFun := fun q ↦ Quotient.liftOn' q (fun x i ↦ Quotient.mk'' (x i)) fun x y hxy ↦ by
    ext i
    simpa using hxy i
  left_inv := fun q ↦ by
    ext i
    simp
  right_inv := fun q ↦ by
    refine Quotient.inductionOn' q fun _ ↦ ?_
    simp only [Quotient.liftOn'_mk'', Quotient.eq'']
    intro i
    change Setoid.r _ _
    rw [← Quotient.eq'']
    simp

end Setoid

import AM.Mathlib.Data.Setoid.Basic
import Mathlib.GroupTheory.Coset.Basic

open Function MulOpposite Set
open scoped Pointwise

variable {α : Type*}

namespace QuotientGroup

variable [Group α] (s : Subgroup α)

@[to_additive]
lemma leftRel_prod {β : Type*} [Group β] (s' : Subgroup β) :
    leftRel (s.prod s') = (leftRel s).prod (leftRel s') := by
  refine Setoid.ext fun x y ↦ ?_
  rw [Setoid.prod_apply]
  simp_rw [leftRel_apply]
  rfl

@[to_additive]
lemma rightRel_prod {β : Type*} [Group β] (s' : Subgroup β) :
    rightRel (s.prod s') = (rightRel s).prod (rightRel s') := by
  refine Setoid.ext fun x y ↦ ?_
  rw [Setoid.prod_apply]
  simp_rw [rightRel_apply]
  rfl

@[to_additive]
lemma leftRel_pi {ι : Type*} {β : ι → Type*} [∀ i, Group (β i)] (s' : ∀ i, Subgroup (β i)) :
    leftRel (Subgroup.pi Set.univ s') = @piSetoid _ _ fun i ↦ leftRel (s' i) := by
  refine Setoid.ext fun x y ↦ ?_
  simp [Setoid.piSetoid_apply, leftRel_apply, Subgroup.mem_pi]

@[to_additive]
lemma rightRel_pi {ι : Type*} {β : ι → Type*} [∀ i, Group (β i)] (s' : ∀ i, Subgroup (β i)) :
    rightRel (Subgroup.pi Set.univ s') = @piSetoid _ _ fun i ↦ rightRel (s' i) := by
  refine Setoid.ext fun x y ↦ ?_
  simp [Setoid.piSetoid_apply, rightRel_apply, Subgroup.mem_pi]

end QuotientGroup

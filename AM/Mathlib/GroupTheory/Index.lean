import AM.Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

namespace Subgroup

open BigOperators Cardinal

variable {G : Type*} [Group G] (H K L : Subgroup G)

variable {H}

@[to_additive]
lemma finite_quotient_of_finite_quotient_of_index_ne_zero {X : Type*} [MulAction G X]
    (hq : Finite <| MulAction.orbitRel.Quotient G X) (hi : H.index ≠ 0) :
    Finite <| MulAction.orbitRel.Quotient H X := by
  have := fintypeOfIndexNeZero hi
  exact MulAction.finite_quotient_of_finite_quotient_of_finite_quotient hq inferInstance

@[to_additive]
lemma finite_quotient_of_pretransitive_of_index_ne_zero {X : Type*} [MulAction G X]
    [MulAction.IsPretransitive G X] (hi : H.index ≠ 0) :
    Finite <| MulAction.orbitRel.Quotient H X := by
  have := (MulAction.pretransitive_iff_subsingleton_quotient G X).1 inferInstance
  exact finite_quotient_of_finite_quotient_of_index_ne_zero (Finite.of_subsingleton) hi

end Subgroup

import AM.Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Index

namespace Subgroup

open Cardinal

variable {G G' : Type*} [Group G] [Group G'] (H K L : Subgroup G)

@[to_additive]
lemma index_prod (H : Subgroup G) (K : Subgroup G') : (H.prod K).index = H.index * K.index := by
  simp_rw [index, ← Nat.card_prod]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.prodQuotientEquiv _ _).symm)
  rw [QuotientGroup.leftRel_prod]

@[to_additive]
lemma index_pi {ι : Type*} [Fintype ι] (H : ι → Subgroup G) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

@[simp]
lemma index_toAddSubgroup : (Subgroup.toAddSubgroup H).index = H.index :=
  rfl

@[simp]
lemma _root_.AddSubgroup.index_toSubgroup {G : Type*} [AddGroup G] (H : AddSubgroup G) :
    (AddSubgroup.toSubgroup H).index = H.index :=
  rfl

end Subgroup

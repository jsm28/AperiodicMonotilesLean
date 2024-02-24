import Mathlib.Logic.Equiv.Defs

open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

namespace Equiv

@[simp] lemma _root_.EquivLike.apply_coe_symm_apply {F} [EquivLike F α β] (e : F) (x : β) :
    e ((e : α ≃ β).symm x) = x :=
  (e : α ≃ β).apply_symm_apply x

@[simp] lemma _root_.EquivLike.coe_symm_apply_apply {F} [EquivLike F α β] (e : F) (x : α) :
    (e : α ≃ β).symm (e x) = x :=
  (e : α ≃ β).symm_apply_apply x

@[simp] lemma _root_.EquivLike.coe_symm_comp_self {F} [EquivLike F α β] (e : F) :
    (e : α ≃ β).symm ∘ e = id :=
  (e : α ≃ β).symm_comp_self

@[simp] lemma _root_.EquivLike.self_comp_coe_symm {F} [EquivLike F α β] (e : F) :
    e ∘ (e : α ≃ β).symm = id :=
  (e : α ≃ β).self_comp_symm

end Equiv

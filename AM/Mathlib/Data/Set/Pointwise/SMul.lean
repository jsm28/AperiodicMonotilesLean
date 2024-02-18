import Mathlib.Data.Set.Pointwise.SMul

open Function MulOpposite

variable {F α β γ : Type*}

namespace Set

open Pointwise

section Group

variable [Group α] [MulAction α β] {s t A B : Set β} {a : α} {x : β}

@[to_additive (attr := simp)]
lemma smul_set_disjoint_iff : Disjoint (a • s) (a • t) ↔ Disjoint s t := by
  simp [disjoint_iff, ←smul_set_inter]

end Group

end Set

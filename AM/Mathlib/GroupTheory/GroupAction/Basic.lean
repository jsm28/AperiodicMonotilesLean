import Mathlib.GroupTheory.GroupAction.Basic

universe u v

open Pointwise

open Function

namespace MulAction

variable {G α β : Type*} [Group G] [MulAction G α] [MulAction G β]

section Stabilizer

variable (G α)

@[to_additive (attr := simp)]
lemma stabilizer_univ : stabilizer G (Set.univ : Set α) = ⊤ := by
  ext
  simp

end Stabilizer

end MulAction

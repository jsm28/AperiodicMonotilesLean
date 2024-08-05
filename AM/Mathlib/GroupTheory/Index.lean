import Mathlib.GroupTheory.Index

namespace Subgroup

variable {G : Type*} [Group G] (H : Subgroup G)

variable {H}

@[to_additive]
lemma index_eq_zero_iff_infinite : H.index = 0 ↔ Infinite (G ⧸ H) := by
  simp [index, Nat.card_eq_zero]

end Subgroup

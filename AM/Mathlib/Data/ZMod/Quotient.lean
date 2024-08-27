import Mathlib.Data.ZMod.Quotient


open QuotientAddGroup Set ZMod

variable (n : ℕ) {A R : Type*} [AddGroup A] [Ring R]

namespace Int

@[simp]
lemma index_zmultiples (a : ℤ) : (AddSubgroup.zmultiples a).index = a.natAbs := by
  rw [AddSubgroup.index, Nat.card_congr (quotientZMultiplesEquivZMod a).toEquiv, Nat.card_zmod]

end Int

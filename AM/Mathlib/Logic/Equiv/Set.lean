import Mathlib.Logic.Equiv.Set

open Set

namespace Equiv

lemma setOf_apply_symm_eq_image_setOf {α β} (e : α ≃ β) (p : α → Prop) :
    {b | p (e.symm b)} = e '' {a | p a} := by
  rw [Equiv.image_eq_preimage, preimage_setOf_eq]

end Equiv

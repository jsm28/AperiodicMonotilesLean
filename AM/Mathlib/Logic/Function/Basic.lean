import Mathlib.Logic.Function.Basic

namespace Function

variable {α β : Sort*} {f : α → β}

lemma funext_iff_of_subsingleton [Subsingleton α] {g : α → β} {x y : α} :
    f x = g y ↔ f = g := by
  refine ⟨fun h ↦ funext fun z ↦ ?_, fun h ↦ ?_⟩
  · rwa [Subsingleton.elim x z, Subsingleton.elim y z] at h
  · rw [h, Subsingleton.elim x y]

end Function

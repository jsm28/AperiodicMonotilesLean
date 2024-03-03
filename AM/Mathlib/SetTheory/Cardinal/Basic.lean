import Mathlib.SetTheory.Cardinal.Basic

open Function Set Order BigOperators Classical

noncomputable section

namespace Cardinal

lemma sInf_eq_zero_iff {s : Set Cardinal} : sInf s = 0 ↔ s = ∅ ∨ ∃ a ∈ s, a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases s.eq_empty_or_nonempty with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨sInf s, csInf_mem hne, h⟩
  · rcases h with rfl | ⟨a, ha, rfl⟩
    · exact Cardinal.sInf_empty
    · exact eq_bot_iff.2 (csInf_le' ha)

lemma iInf_eq_zero_iff {ι : Sort*} {f : ι → Cardinal} :
    (⨅ i, f i) = 0 ↔ IsEmpty ι ∨ ∃ i, f i = 0 := by
  simp [iInf, sInf_eq_zero_iff]

end Cardinal

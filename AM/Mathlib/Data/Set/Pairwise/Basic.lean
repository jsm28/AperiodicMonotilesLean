import Mathlib.Data.Set.Pairwise.Basic

open Set

variable {α β γ ι ι' : Type*} {r p q : α → α → Prop}
section Pairwise

variable {f g : ι → α} {s t u : Set α} {a b : α}

lemma Pairwise.range_pairwise (hr : Pairwise (r on f)) : (Set.range f).Pairwise r := by
  simp only [Set.Pairwise, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact fun _ _ h ↦ hr <| ne_of_apply_ne _ h

end Pairwise

import Mathlib.Data.Set.Pairwise.Basic

open Function Order Set

variable {α ι : Type*}

lemma subsingleton_setOf_mem_iff_pairwise_disjoint {f : ι → Set α} :
    (∀ a, {i | a ∈ f i}.Subsingleton) ↔ Pairwise (Disjoint on f) :=
  ⟨fun h _ _ hij ↦ disjoint_left.2 fun a hi hj ↦ hij (h a hi hj),
   fun h _ _ hx _ hy ↦ by_contra fun hne ↦ disjoint_left.1 (h hne) hx hy⟩

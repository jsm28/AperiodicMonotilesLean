import Mathlib.Logic.Pairwise

open Function

variable {α β : Type*} {r : α → α → Prop}

lemma Pairwise.comp_of_injective (hr : Pairwise r) {f : β → α} (hf : Injective f) :
    Pairwise (r on f) :=
  fun _ _ h ↦ hr <| hf.ne h

lemma Pairwise.of_comp_of_surjective {f : β → α} (hr : Pairwise (r on f)) (hf : Surjective f) :
    Pairwise r := hf.forall₂.2 fun _ _ h ↦ hr <| ne_of_apply_ne f h

lemma Function.Bijective.pairwise_comp_iff {f : β → α} (hf : Bijective f) :
    Pairwise (r on f) ↔ Pairwise r :=
  ⟨fun hr ↦ hr.of_comp_of_surjective hf.surjective, fun hr ↦ hr.comp_of_injective hf.injective⟩

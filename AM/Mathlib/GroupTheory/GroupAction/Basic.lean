import Mathlib.GroupTheory.GroupAction.Basic

open Function

namespace MulAction
variable {M G α : Type*} [Group G] [Monoid M] [MulAction G α] [MulAction M α]

@[to_additive]
lemma fst_mem_orbit_of_mem_orbit {β : Type*} [MulAction M β] {x y : α × β}
    (h : x ∈ MulAction.orbit M y) : x.1 ∈ MulAction.orbit M y.1 := by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]
lemma snd_mem_orbit_of_mem_orbit {β : Type*} [MulAction M β] {x y : α × β}
    (h : x ∈ MulAction.orbit M y) : x.2 ∈ MulAction.orbit M y.2 := by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

variable (G α)

@[to_additive]
lemma orbitRel_le_fst (β : Type*) [MulAction G β] :
    orbitRel G (α × β) ≤ (orbitRel G α).comap Prod.fst :=
  Setoid.le_def.2 fst_mem_orbit_of_mem_orbit

@[to_additive]
lemma orbitRel_le_snd (β : Type*) [MulAction G β] :
    orbitRel G (α × β) ≤ (orbitRel G β).comap Prod.snd :=
  Setoid.le_def.2 snd_mem_orbit_of_mem_orbit

end MulAction

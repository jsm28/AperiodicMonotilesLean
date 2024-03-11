import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Pairwise
import Mathlib.Order.SetNotation

open Function Set

namespace Equiv

namespace Set

/-- If an indexed family of sets is pairwise disjoint, their union is equivalent to the sigma
type of those sets. -/
protected noncomputable def iUnion {α β : Type*} {f : α → Set β} (h : Pairwise (Disjoint on f)) :
    ⋃ i, f i ≃ Σi, f i := by
  calc ⋃ i, f i ≃ { x : (α × β) | x.2 ∈ f x.1 } :=
      (Equiv.ofBijective (fun x ↦ ⟨(x : α × β).2, Set.mem_iUnion.2 ⟨(x : α × β).1, x.property⟩⟩)
         ⟨fun x y hxy ↦ by
            simp only [mem_setOf_eq, Subtype.mk.injEq] at hxy
            ext
            · by_contra hne
              replace h := Set.disjoint_left.1 (h hne) x.property
              rw [hxy] at h
              exact h y.property
            · exact hxy,
          fun x ↦ by
            rcases Set.mem_iUnion.1 x.property with ⟨i, hi⟩
            exact ⟨⟨(i, ↑x), hi⟩, rfl⟩⟩).symm
    _ ≃ Σi, { y : β | (i, y) ∈ { x : (α × β) | x.2 ∈ f x.1 } } := setProdEquivSigma _
    _ ≃ Σi, f i := sigmaCongrRight fun i ↦ setCongr (by simp)
end Set

end Equiv

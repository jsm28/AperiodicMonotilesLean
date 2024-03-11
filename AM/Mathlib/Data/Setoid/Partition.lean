import Mathlib.Data.Setoid.Partition
import AM.Mathlib.Logic.Equiv.Set

variable {α : Type*} {β : Type*}

namespace Setoid

variable (r : Setoid α) (f : α → β)
variable {r f}

/-- Given two equivalence relations with `r ≤ s`, a bijection between the sum of the quotients by
`r` on each equivalence class by `s` and the quotient by `r`. -/
noncomputable def equivSigmaFibersOfLe {r s : Setoid α} (hle : r ≤ s) :
    (Σq : Quotient s, Quotient (r.comap (Subtype.val : Quotient.mk s ⁻¹' {q} → α))) ≃
      Quotient r := by
  calc
    (Σq : Quotient s, Quotient (r.comap (Subtype.val : Quotient.mk s ⁻¹' {q} → α))) ≃
      Σq : Quotient s, (r.comap (Subtype.val : Quotient.mk s ⁻¹' {q} → α)).classes :=
        Equiv.sigmaCongrRight fun x ↦ Setoid.quotientEquivClasses _
    _ ≃ Σq : Quotient s, (fun t ↦ (Subtype.val '' t)) ''
          (r.comap (Subtype.val : Quotient.mk s ⁻¹' {q} → α)).classes :=
        Equiv.sigmaCongrRight (fun x ↦ Equiv.Set.image _ _
          (fun y z h ↦ (Set.image_eq_image Subtype.val_injective).1 h))
    _ ≃ ⋃ q : Quotient s, (fun t ↦ (Subtype.val '' t)) ''
          (r.comap (Subtype.val : Quotient.mk s ⁻¹' {q} → α)).classes :=
        (Equiv.Set.iUnion fun i j hij ↦ Set.disjoint_left.2 fun c hc ↦ by
          rcases hc with ⟨k, hk, rfl⟩
          simp only [Set.mem_image, not_exists, not_and]
          intro k' hk' he
          have hd : Disjoint (Subtype.val '' k) (Subtype.val '' k') := by
            by_contra hd
            simp only [Set.not_disjoint_iff, Set.mem_image, Subtype.exists, Set.mem_preimage,
                       Set.mem_singleton_iff, exists_and_right, exists_eq_right] at hd
            rcases hd with ⟨x, ⟨rfl, hi⟩, ⟨rfl, hj⟩⟩
            exact hij rfl
          simp only [he, disjoint_self, Set.bot_eq_empty, Set.image_eq_empty] at hd
          exact Set.not_nonempty_iff_eq_empty.2 hd
            (nonempty_of_mem_partition (isPartition_classes _) hk)).symm
    _ ≃ r.classes := Equiv.setCongr (by
          ext x
          simp only [Set.mem_iUnion, Set.mem_image, Setoid.classes, Subtype.exists,
                     Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
          refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
          · rcases h with ⟨q, x', ⟨x, rfl, rfl⟩, rfl⟩
            refine ⟨x, ?_⟩
            ext y
            simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, Set.mem_preimage,
                       Set.mem_singleton_iff, exists_and_right, exists_eq_right]
            simp_rw [← Quotient.mk''_eq_mk, Quotient.eq'']
            refine ⟨fun h ↦ ?_, fun h ↦ ⟨le_def.1 hle h, h⟩⟩
            rcases h with ⟨_, h'⟩
            exact h'
          · rcases h with ⟨x, rfl⟩
            refine ⟨Quotient.mk s x,
                    quotientEquivClasses (r.comap (Subtype.val : Quotient.mk s ⁻¹' {⟦x⟧} → α))
                      (Quotient.mk _ ⟨x, by simp⟩),
                    ⟨⟨x, ⟨rfl, by simp⟩⟩, ?_⟩⟩
            simp only [quotientEquivClasses_mk_eq]
            ext y
            simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, Set.mem_preimage,
                       Set.mem_singleton_iff, exists_and_right, exists_eq_right]
            simp_rw [← Quotient.mk''_eq_mk, Quotient.eq'']
            refine ⟨fun h ↦ ?_, fun h ↦ ⟨le_def.1 hle h, h⟩⟩
            rcases h with ⟨_, h'⟩
            exact h')
    _ ≃ Quotient r := r.quotientEquivClasses.symm

end Setoid

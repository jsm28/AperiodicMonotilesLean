import Mathlib.GroupTheory.GroupAction.Basic

namespace MulAction
variable {G α : Type*} [Group G] [MulAction G α]

@[to_additive]
lemma orbitRel_subgroupOf (H K : Subgroup G) :
    orbitRel (H.subgroupOf K) α = orbitRel (H ⊓ K : Subgroup G) α := by
  rw [← Subgroup.subgroupOf_map_subtype]
  ext x
  simp_rw [orbitRel_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with ⟨⟨gv, gp⟩, rfl⟩
    simp only [Submonoid.mk_smul]
    refine mem_orbit _ (⟨gv, ?_⟩ : Subgroup.map K.subtype (H.subgroupOf K))
    simpa using gp
  · rcases h with ⟨⟨gv, gp⟩, rfl⟩
    simp only [Submonoid.mk_smul]
    simp only [Subgroup.subgroupOf_map_subtype, Subgroup.mem_inf] at gp
    refine mem_orbit _ (⟨⟨gv, ?_⟩, ?_⟩ : H.subgroupOf K)
    · exact gp.2
    · simp only [Subgroup.mem_subgroupOf]
      exact gp.1

end MulAction

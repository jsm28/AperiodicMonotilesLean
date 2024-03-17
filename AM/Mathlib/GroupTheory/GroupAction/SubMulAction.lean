import Mathlib.GroupTheory.GroupAction.SubMulAction

open Function

variable {S T R M : Type*}

namespace SubMulAction

section MulActionMonoid

variable [Monoid R] [MulAction R M]

lemma mem_orbit_subMul_iff {p : SubMulAction R M} {x m : p} :
    x ∈ MulAction.orbit R m ↔ (x : M) ∈ MulAction.orbit R (m : M) := by
  erw [← val_image_orbit, Subtype.val_injective.mem_set_image]

end MulActionMonoid

section MulActionGroup

variable [Group R] [MulAction R M]

lemma orbitRel_of_subMul (p : SubMulAction R M) :
    MulAction.orbitRel R p = (MulAction.orbitRel R M).comap Subtype.val := by
  refine Setoid.ext_iff.2 (fun x y ↦ ?_)
  rw [Setoid.comap_rel]
  exact mem_orbit_subMul_iff

end MulActionGroup

end SubMulAction

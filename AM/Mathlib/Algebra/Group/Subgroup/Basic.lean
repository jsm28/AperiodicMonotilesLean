import Mathlib.Algebra.Group.Subgroup.Basic

open Function
open Int

variable {G : Type*} [Group G]

namespace Subgroup

@[to_additive (attr := simp)]
lemma inclusion_inj {H K : Subgroup G} (h : H ≤ K) {x y : H} :
    inclusion h x = inclusion h y ↔ x = y :=
  (inclusion_injective h).eq_iff

end Subgroup

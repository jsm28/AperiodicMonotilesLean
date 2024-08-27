import Mathlib.Algebra.Module.Submodule.Map

open Function Pointwise Set

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

namespace Submodule

section AddCommGroup

variable [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M)
variable [AddCommGroup M₂] [Module R M₂]

lemma map_toAddSubgroup (f : M →ₗ[R] M₂) (p : Submodule R M) :
    (p.map f).toAddSubgroup = p.toAddSubgroup.map (f : M →+ M₂) :=
  SetLike.coe_injective rfl

end AddCommGroup

end Submodule

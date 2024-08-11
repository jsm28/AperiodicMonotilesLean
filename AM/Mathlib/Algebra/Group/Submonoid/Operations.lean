import Mathlib.Algebra.Group.Submonoid.Operations

namespace MonoidHom

variable {M N : Type*} [MulOneClass M] [MulOneClass N] (S : Submonoid M)

open Submonoid

-- proof taken from AlgHom.injective_codRestrict

@[to_additive (attr := simp)]
lemma injective_codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M →* N) (s : S)
    (h : ∀ x, f x ∈ s) : Function.Injective (f.codRestrict s h) ↔ Function.Injective f :=
  ⟨fun H _ _ hxy ↦ H <| Subtype.eq hxy, fun H _ _ hxy ↦ H (congr_arg Subtype.val hxy)⟩

end MonoidHom

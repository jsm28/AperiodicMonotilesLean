/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Combinatorics.Tiling.Basic
import AM.Mathlib.Logic.Function.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Periodic tilings and aperiodic protosets

This file defines the properties of a tiling being (strongly or weakly) periodic, and of a
protoset being (weakly or strongly) aperiodic.

By analogy to definitions in a continuous context, we say that a tiling in a discrete context
is strongly periodic if the quotient of the underlying space by the symmetry group of the tiling
is finite. We say it is weakly periodic if the symmetry group includes an element of infinite
order, or, more generally, that it is weakly `n`-periodic if it includes a `ℤ^n` subgroup. Note
that weak periodicity is sometimes defined in the literature as a tiling being a finite union of
subsets, each of which is weakly periodic in the sense used here. A protoset is then weakly
aperiodic if it admits a tiling but not a strongly periodic tiling, and strongly aperiodic if it
admits a tiling but not a weakly periodic tiling.

## Main definitions

* `TileSet.StronglyPeriodic t`: A `TileSetFunction` for the property of `t` being strongly
periodic.

* `TileSet.WeaklyPeriodic n t`: A `TileSetFunction` for the property of `t` being weakly
`n`-periodic.

* `Protoset.WeaklyAperiodic`: The property of a protoset being weakly aperiodic.

* `Protoset.StronglyAperiodic`: The property of a protoset being strongly aperiodic.

## References

* Branko Grünbaum and G. C. Shephard, Tilings and Patterns, 1987
* Chaim Goodman-Strauss, [Open Questions in
  Tiling](https://strauss.hosted.uark.edu/papers/survey.pdf)
* Rachel Greenfeld and Terence Tao, [A counterexample to the periodic tiling
  conjecture](https://arxiv.org/abs/2211.15847)
-/


noncomputable section

namespace Discrete

open Function
open scoped Cardinal Pointwise

variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}

namespace TileSet

/-- Whether a `TileSet` is strongly periodic: that is, whether its symmetry group has only
finitely many orbits of points of `X` under its action. -/
def StronglyPeriodic : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ Infinite <| MulAction.orbitRel.Quotient t.symmetryGroup X,
   by
     refine fun {ιₜ ιₜ'} (f t) ↦ ?_
     simp only [eq_iff_iff]
     refine Equiv.infinite_iff (Quotient.congrRight fun x y ↦ ?_)
     change _ ∈ MulAction.orbit _ _ ↔ _ ∈ MulAction.orbit _ _
     simp [MulAction.mem_orbit_iff],
   by
     refine fun {ιₜ g} (t _) ↦ ?_
     simp only [eq_iff_iff]
     refine Equiv.infinite_iff (Quotient.congr (MulAction.toPerm g⁻¹) fun x y ↦ ?_)
     change _ ∈ MulAction.orbit _ _ ↔ _ ∈ MulAction.orbit _ _
     simp only [MulAction.mem_orbit_iff, Subtype.exists, Submonoid.mk_smul, exists_prop,
                MulAction.toPerm_apply]
     refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
     · rcases ha with ⟨ha, rfl⟩
       rw [mem_symmetryGroup_smul_iff'] at ha
       exact ⟨g⁻¹ * a * g, ha, by simp [mul_smul]⟩
     · rcases ha with ⟨ha, ha'⟩
       rw [← mem_symmetryGroup_smul_iff g] at ha
       exact ⟨g * a * g⁻¹, ha, by simp [mul_smul, ha']⟩⟩

lemma stronglyPeriodic_iff {t : TileSet ps ιₜ} :
    TileSet.StronglyPeriodic t ↔ Infinite (MulAction.orbitRel.Quotient t.symmetryGroup X) :=
  Iff.rfl

/-- Whether a `TileSet` is `n`-weakly periodic: that is, whether its symmetry group has a `ℤ^n`
subgroup. -/
def WeaklyPeriodic (n : ℕ) : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦
     ∃ f : (Fin n → Multiplicative ℤ) →* t.symmetryGroup, Injective f,
   by
     refine fun {ιₜ ιₜ'} (e t) ↦ ?_
     simp only [eq_iff_iff]
     refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun ⟨f, hf⟩ ↦ ?_⟩
     · refine ⟨(MulEquiv.subgroupCongr (t.symmetryGroup_reindex e.symm)).toMonoidHom.comp f, ?_⟩
       simpa [Injective] using hf
     · refine ⟨(MulEquiv.subgroupCongr (t.symmetryGroup_reindex e.symm).symm).toMonoidHom.comp f,
               ?_⟩
       simpa [Injective] using hf,
   by
     refine fun {ιₜ g} (t _) ↦ ?_
     simp only [eq_iff_iff]
     refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun ⟨f, hf⟩ ↦ ?_⟩
     · refine ⟨((MulEquiv.subgroupCongr (t.symmetryGroup_smul g)).trans
         (Subgroup.equivSMul _ _).symm).toMonoidHom.comp f, ?_⟩
       simpa [Injective] using hf
     · refine ⟨((Subgroup.equivSMul _ _).trans
         (MulEquiv.subgroupCongr (t.symmetryGroup_smul g).symm)).toMonoidHom.comp f, ?_⟩
       simpa [Injective] using hf⟩

lemma weaklyPeriodic_iff {n : ℕ} {t : TileSet ps ιₜ} :
    TileSet.WeaklyPeriodic n t ↔ ∃ f : (Fin n → Multiplicative ℤ) →* t.symmetryGroup, Injective f :=
  Iff.rfl

lemma weaklyPeriodic_one_iff {t : TileSet ps ιₜ} :
    TileSet.WeaklyPeriodic 1 t ↔ ∃ g ∈ t.symmetryGroup, ¬IsOfFinOrder g := by
  rw [weaklyPeriodic_iff]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun ⟨g, hg, ho⟩ ↦ ?_⟩
  · refine ⟨f (fun _ ↦ Multiplicative.ofAdd 1), (f (fun _ ↦ Multiplicative.ofAdd 1)).property, ?_⟩
    rw [← injective_zpow_iff_not_isOfFinOrder]
    intro a₁ a₂ h
    dsimp only at h
    simp_rw [← SubgroupClass.coe_zpow, ← map_zpow, ← Subtype.ext_iff, hf.eq_iff, funext_iff,
             Pi.pow_apply, forall_const, ← ofAdd_zsmul] at h
    simpa using h
  · refine ⟨(zpowersHom (t.symmetryGroup) ⟨g, hg⟩).comp (Pi.evalMonoidHom _ 0), ?_⟩
    rw [← injective_zpow_iff_not_isOfFinOrder] at ho
    simp only [Injective, MonoidHom.coe_comp, comp_apply, Pi.evalMonoidHom_apply,
               zpowersHom_apply, Subtype.ext_iff, SubgroupClass.coe_zpow]
    intro a₁ a₂ h
    have h' := ho h
    simpa [funext_iff_of_subsingleton] using h'

end TileSet

namespace Protoset

variable (ιₜ) {s : Subgroup G}

/-- Whether `ps` is weakly aperiodic (for `TileSet ps ιₜ` that satisfy the property `p`); that is,
whether it has such a `TileSet`, but none is strongly periodic. -/
def WeaklyAperiodic (p : TileSetFunction ps Prop s) : Prop :=
  (∃ t : TileSet ps ιₜ, p t) ∧ ∀ t : TileSet ps ιₜ, ¬ TileSet.StronglyPeriodic t

/-- Whether `ps` is strongly aperiodic (for `TileSet ps ιₜ` that satisfy the property `p`); that
is, whether it has such a `TileSet`, but none is weakly periodic. -/
def StronglyAperiodic (p : TileSetFunction ps Prop s) : Prop :=
  (∃ t : TileSet ps ιₜ, p t) ∧ ∀ t : TileSet ps ιₜ, ¬ TileSet.WeaklyPeriodic 1 t

end Protoset

end Discrete

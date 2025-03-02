/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Combinatorics.Tiling.Function.Tiling
import AM.Mathlib.Combinatorics.Tiling.Isohedral
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Group.TypeTags
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.FreeModule.Int

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

* `t.StronglyPeriodic`: A `TileSetFunction` for the property of `t` being strongly
periodic.

* `t.WeaklyPeriodic n`: A `TileSetFunction` for the property of `t` being weakly
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
open scoped Cardinal Nat Pointwise

variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}

namespace TileSet

/-- Whether a `TileSet` is strongly periodic: that is, whether its symmetry group has only
finitely many orbits of points of `X` under its action. -/
def StronglyPeriodic : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ Finite <| MulAction.orbitRel.Quotient t.symmetryGroup X,
   by
     refine fun {ιₜ ιₜ'} (f t) ↦ ?_
     simp only [eq_iff_iff]
     refine Equiv.finite_iff (Quotient.congrRight fun x y ↦ ?_)
     simp [MulAction.orbitRel_apply, MulAction.mem_orbit_iff],
   by
     refine fun {ιₜ g} (t _) ↦ ?_
     simp only [eq_iff_iff]
     refine Equiv.finite_iff (Quotient.congr (MulAction.toPerm g⁻¹) fun x y ↦ ?_)
     simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subtype.exists,
                Submonoid.mk_smul, exists_prop, MulAction.toPerm_apply]
     refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
     · rcases ha with ⟨ha, rfl⟩
       rw [mem_symmetryGroup_smul_iff'] at ha
       exact ⟨g⁻¹ * a * g, ha, by simp [mul_smul]⟩
     · rcases ha with ⟨ha, ha'⟩
       rw [← mem_symmetryGroup_smul_iff g] at ha
       simp only [Subgroup.mk_smul] at ha'
       exact ⟨g * a * g⁻¹, ha, by simp [mul_smul, ha']⟩⟩

lemma stronglyPeriodic_iff {t : TileSet ps ιₜ} :
    t.StronglyPeriodic ↔ Finite (MulAction.orbitRel.Quotient t.symmetryGroup X) :=
  Iff.rfl

lemma stronglyPeriodic_of_finite_quotient_of_index_ne_zero {t : TileSet ps ιₜ}
    [Finite <| MulAction.orbitRel.Quotient G X] (hi : t.symmetryGroup.index ≠ 0) :
    t.StronglyPeriodic :=
  Subgroup.finite_quotient_of_finite_quotient_of_index_ne_zero hi

lemma stronglyPeriodic_of_pretransitive_of_index_ne_zero {t : TileSet ps ιₜ}
    [MulAction.IsPretransitive G X] (hi : t.symmetryGroup.index ≠ 0) :
    t.StronglyPeriodic :=
  Subgroup.finite_quotient_of_pretransitive_of_index_ne_zero hi

lemma StronglyPeriodic.finite_quotient {t : TileSet ps ιₜ} (h : t.StronglyPeriodic) :
    Finite <| MulAction.orbitRel.Quotient G X := by
  rw [stronglyPeriodic_iff, (MulAction.equivSubgroupOrbits X t.symmetryGroup).finite_iff] at h
  by_contra hi
  revert h
  rw [imp_false]
  rw [not_finite_iff_infinite] at hi ⊢
  suffices ∀ ω : MulAction.orbitRel.Quotient G X, Nonempty
      (MulAction.orbitRel.Quotient t.symmetryGroup (MulAction.orbitRel.Quotient.orbit ω)) by
    infer_instance
  intro ω
  rw [nonempty_quotient_iff]
  simpa using ω.orbit_nonempty

lemma StronglyPeriodic.index_ne_zero_of_free [Nonempty X] {t : TileSet ps ιₜ}
    (h : t.StronglyPeriodic) {H : Subgroup G} (free : ∀ x : X, MulAction.stabilizer H x = ⊥)
    (hi : H.index ≠ 0) : t.symmetryGroup.index ≠ 0 := by
  rw [stronglyPeriodic_iff] at h
  have hr : H.relindex t.symmetryGroup ≠ 0 := mt Subgroup.index_eq_zero_of_relindex_eq_zero hi
  suffices t.symmetryGroup.relindex H ≠ 0 by
    rw [← Subgroup.relindex_top_right] at hi ⊢
    exact Subgroup.relindex_ne_zero_trans this hi
  rw [Subgroup.relindex] at hr ⊢
  have hf := Subgroup.finite_quotient_of_finite_quotient_of_index_ne_zero hr (X := X)
  rw [MulAction.orbitRel.Quotient, MulAction.orbitRel_subgroupOf, inf_comm,
      ← MulAction.orbitRel_subgroupOf, ← MulAction.orbitRel.Quotient,
      (MulAction.equivSubgroupOrbits X _).finite_iff] at hf
  intro h0
  rw [Subgroup.index_eq_zero_iff_infinite] at h0
  revert hf
  rw [imp_false, not_finite_iff_infinite]
  have hne : Nonempty (MulAction.orbitRel.Quotient H X) := by simpa [nonempty_quotient_iff]
  have x := Classical.arbitrary (MulAction.orbitRel.Quotient H X)
  convert Infinite.sigma_of_right (a := x)
  have y : MulAction.orbitRel.Quotient.orbit x :=
    (MulAction.orbitRel.Quotient.orbit_nonempty x).to_subtype.some
  rw [(MulAction.equivSubgroupOrbitsQuotientGroup y _ _).infinite_iff]
  · exact h0
  · intro z
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
    refine ⟨fun hs ↦ ?_, fun hs ↦ by simp [hs]⟩
    suffices g ∈ MulAction.stabilizer H (z : X) by
      simpa [free] using this
    rw [MulAction.mem_stabilizer_iff, ← MulAction.orbitRel.Quotient.orbit.coe_smul, hs]

lemma StronglyPeriodic.finite_quotient_tilePoint {t : TileSet ps ιₜ} (h : t.StronglyPeriodic)
    (hf : t.FiniteDistinctIntersections) :
    Finite (MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) := by
  rw [← Set.finite_univ_iff, ← Set.preimage_univ (f := t.quotientPointOfquotientTilePoint),
      ← Set.biUnion_preimage_singleton]
  rw [stronglyPeriodic_iff] at h
  refine Finite.Set.finite_biUnion _ _ fun x _ ↦ ?_
  induction' x using Quotient.inductionOn' with x
  rw [@Quotient.mk''_eq_mk]
  exact finite_preimage_quotientPointOfquotientTilePoint x
    (FiniteDistinctIntersections.finiteDistinctIntersectionsOn {x} hf)

lemma stronglyPeriodic_of_finite_quotient_tilePoint {t : TileSet ps ιₜ}
    (hf : Finite (MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}))
    (hu : t.UnionEqUniv) : t.StronglyPeriodic := by
  rw [stronglyPeriodic_iff]
  rw [← Set.finite_univ_iff] at hf ⊢
  exact Set.Finite.of_surjOn t.quotientPointOfquotientTilePoint
    (Set.surjective_iff_surjOn_univ.1 (surjective_quotientPointOfquotientTilePoint hu)) hf

lemma stronglyPeriodic_of_isohedralNumber_lt_aleph0 {t : TileSet ps ιₜ} (h : t.isohedralNumber < ℵ₀)
    (hf : ∀ i, (t i : Set X).Finite) (hu : t.UnionEqUniv) : t.StronglyPeriodic :=
  stronglyPeriodic_of_finite_quotient_tilePoint
    (finite_quotient_tilePoint_of_isohedralNumber_lt_aleph0 h hf) hu

lemma StronglyPeriodic.isohedralNumber_lt_aleph0 {t : TileSet ps ιₜ} (h : t.StronglyPeriodic)
    (hf : t.FiniteDistinctIntersections) (hn : ∀ i, (t i : Set X).Nonempty) :
    t.isohedralNumber < ℵ₀ :=
  isohedralNumber_lt_aleph0_of_finite_quotient_tilePoint
    (StronglyPeriodic.finite_quotient_tilePoint h hf) hn

lemma stronglyPeriodic_iff_isohedralNumber_lt_aleph0 {t : TileSet ps ιₜ} (ht : t.IsTiling)
    (hf : ∀ i, (t i : Set X).Finite) (hn : ∀ i, (t i : Set X).Nonempty) :
    t.StronglyPeriodic ↔ t.isohedralNumber < ℵ₀ :=
  ⟨fun h ↦ StronglyPeriodic.isohedralNumber_lt_aleph0 h
    (IsTiling.finiteDistinctIntersections ht) hn,
   fun h ↦ stronglyPeriodic_of_isohedralNumber_lt_aleph0 h hf (IsTiling.unionEqUniv ht)⟩

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
    t.WeaklyPeriodic n ↔ ∃ f : (Fin n → Multiplicative ℤ) →* t.symmetryGroup, Injective f :=
  Iff.rfl

lemma weaklyPeriodic_zero (t : TileSet ps ιₜ) : t.WeaklyPeriodic 0 :=
  ⟨1, injective_of_subsingleton _⟩

lemma weaklyPeriodic_one_iff {t : TileSet ps ιₜ} :
    t.WeaklyPeriodic 1 ↔ ∃ g ∈ t.symmetryGroup, ¬IsOfFinOrder g := by
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

lemma weaklyPeriodic_of_le {t : TileSet ps ιₜ} {m n : ℕ} (h : t.WeaklyPeriodic n) (hle : m ≤ n) :
    t.WeaklyPeriodic m := by
  rcases h with ⟨f, hf⟩
  exact ⟨f.comp (ExtendByOne.hom (Multiplicative ℤ) (Fin.castLE hle)),
         hf.comp (extend_injective (Fin.strictMono_castLE hle).injective _)⟩

lemma weaklyPeriodic_iff_of_relindex_ne_zero {n : ℕ} {t : TileSet ps ιₜ} {H : Subgroup G}
    (hi : H.relindex t.symmetryGroup ≠ 0) :
    t.WeaklyPeriodic n ↔
      ∃ f : (Fin n → Multiplicative ℤ) →* (H ⊓ t.symmetryGroup : Subgroup G), Injective f := by
  refine ⟨fun ⟨f, hf⟩ ↦ ?_,
    fun ⟨f, hf⟩ ↦ ⟨(Subgroup.inclusion inf_le_right).comp f, fun x y hxy ↦ hf (by simpa using hxy)⟩⟩
  let f' : (Fin n → Multiplicative ℤ) →* (Fin n → Multiplicative ℤ) :=
    powMonoidHom (H.relindex t.symmetryGroup)!
  have hf' : Injective f' := by
    intro x₁ x₂ he
    simp only [powMonoidHom_apply, f'] at he
    ext i
    suffices (x₁ i) ^ (H.relindex t.symmetryGroup)! = (x₂ i) ^ (H.relindex t.symmetryGroup)! by
      rwa [← zpow_natCast, ← zpow_natCast, zpow_left_inj (mod_cast (Nat.factorial_ne_zero _))]
        at this
    simp_rw [← Pi.pow_apply, he]
  have h : ∀ x : Fin n → Multiplicative ℤ,
      (((Subgroup.subtype _).comp f).comp f') x ∈ H ⊓ t.symmetryGroup := by
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, comp_apply, f', powMonoidHom_apply,
               map_pow, SubmonoidClass.coe_pow]
    exact fun x ↦ Subgroup.pow_mem_of_relindex_ne_zero_of_dvd hi (SetLike.coe_mem _)
      (fun _ ↦ Nat.dvd_factorial)
  refine ⟨(((Subgroup.subtype _).comp f).comp f').codRestrict _ h, ?_⟩
  simp only [MonoidHom.injective_codRestrict, MonoidHom.coe_comp, Subgroup.coe_subtype]
  exact (Subtype.val_injective.comp hf).comp hf'

lemma weaklyPeriodic_iff_of_index_ne_zero {n : ℕ} {t : TileSet ps ιₜ} {H : Subgroup G}
    (hi : H.index ≠ 0) :
    t.WeaklyPeriodic n ↔
      ∃ f : (Fin n → Multiplicative ℤ) →* (H ⊓ t.symmetryGroup : Subgroup G), Injective f :=
  weaklyPeriodic_iff_of_relindex_ne_zero (mt Subgroup.index_eq_zero_of_relindex_eq_zero hi)

/-- In a space with a ℤ^n subgroup of finite index, where `X` has finite quotient by the action
of `G`, a weakly `n`-periodic `TileSet` is strongly periodic. -/
lemma WeaklyPeriodic.stronglyPeriodic_of_finite_quotient_of_equiv_of_index_ne_zero {n : ℕ}
    {t : TileSet ps ιₜ} (h : t.WeaklyPeriodic n) [Finite <| MulAction.orbitRel.Quotient G X]
    {H : Subgroup G} (e : H ≃* (Fin n → Multiplicative ℤ)) (hi : H.index ≠ 0) :
    t.StronglyPeriodic := by
  refine stronglyPeriodic_of_finite_quotient_of_index_ne_zero ?_
  rw [weaklyPeriodic_iff_of_index_ne_zero hi] at h
  rcases h with ⟨f, hf⟩
  rw [← Subgroup.relindex_top_right] at hi ⊢
  refine Subgroup.relindex_ne_zero_trans ?_ hi
  rw [← Subgroup.inf_relindex_left]
  suffices (f.range.map (Subgroup.subtype _)).relindex H ≠ 0 from
    mt (Subgroup.relindex_eq_zero_of_le_left (Subgroup.map_subtype_le f.range)) this
  let f' : f.range ≃* (Fin n → Multiplicative ℤ) :=
    ((MulEquiv.subgroupCongr f.range_eq_map).trans (Subgroup.equivMapOfInjective _ _ hf).symm).trans
    Subgroup.topEquiv
  let e' : (Fin n → Multiplicative ℤ) →* H := ↑e.symm
  have he' : Surjective e' := e.symm.surjective
  rw [Subgroup.relindex, ← Subgroup.index_comap_of_surjective _ he',
      Int.subgroup_index_ne_zero_iff]
  exact ⟨((((MulEquiv.subgroupCongr
    (((Subgroup.map (H ⊓ t.symmetryGroup).subtype f.range).subgroupOf H).map_equiv_eq_comap_symm
      e).symm).trans (Subgroup.equivMapOfInjective _ _ e.injective).symm).trans
    (Subgroup.subgroupOfEquivOfLe ((Subgroup.map_subtype_le _).trans inf_le_left))).trans
    (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).symm).trans f'⟩

/-- In a space with a ℤ^n subgroup of finite index, where `G` acts transitively on `X`, a weakly
`n`-periodic `TileSet` is strongly periodic. -/
lemma WeaklyPeriodic.stronglyPeriodic_of_pretransitive_of_equiv_of_index_ne_zero {n : ℕ}
    {t : TileSet ps ιₜ} (h : t.WeaklyPeriodic n) [MulAction.IsPretransitive G X] {H : Subgroup G}
    (e : H ≃* (Fin n → Multiplicative ℤ)) (hi : H.index ≠ 0) : t.StronglyPeriodic := by
  have : Subsingleton <| MulAction.orbitRel.Quotient G X :=
    (MulAction.pretransitive_iff_subsingleton_quotient _ _).1 inferInstance
  exact WeaklyPeriodic.stronglyPeriodic_of_finite_quotient_of_equiv_of_index_ne_zero h e hi

/-- In a space with a ℤ^n subgroup of finite index acting freely, a strongly periodic `TileSet`
is weakly `n`-periodic. -/
lemma StronglyPeriodic.weaklyPeriodic_of_equiv_of_free [Nonempty X] {n : ℕ} {t : TileSet ps ιₜ}
    (h : t.StronglyPeriodic) {H : Subgroup G} (e : H ≃* (Fin n → Multiplicative ℤ))
    (free : ∀ x : X, MulAction.stabilizer H x = ⊥) (hi : H.index ≠ 0) : t.WeaklyPeriodic n := by
  let e' : (Fin n → Multiplicative ℤ) →* H := ↑e.symm
  have he' : Surjective e' := e.symm.surjective
  have hsi := Subgroup.index_inf_ne_zero (StronglyPeriodic.index_ne_zero_of_free h free hi) hi
  rw [← Subgroup.relindex_top_right, ← Subgroup.relindex_inf_mul_relindex, mul_ne_zero_iff,
      Subgroup.relindex_top_right, and_iff_left hi, inf_top_eq, Subgroup.relindex,
      ← Subgroup.index_comap_of_surjective _ he', Int.subgroup_index_ne_zero_iff] at hsi
  rcases hsi with ⟨f⟩
  let f₁ : (Fin n → Multiplicative ℤ) ≃* (t.symmetryGroup ⊓ H : Subgroup G) :=
    (((f.symm.trans
    (MulEquiv.subgroupCongr (Subgroup.map_equiv_eq_comap_symm _ _).symm)).trans
    (Subgroup.equivMapOfInjective _ _ e.injective).symm).trans
    (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right _ _).symm)).trans
    (Subgroup.subgroupOfEquivOfLe inf_le_right)
  let f₂ : (Fin n → Multiplicative ℤ) →* (t.symmetryGroup ⊓ H : Subgroup G) := ↑f₁
  have hf₂ : Injective f₂ := f₁.injective
  let f₃ : (t.symmetryGroup ⊓ H : Subgroup G) →* t.symmetryGroup := Subgroup.inclusion inf_le_left
  have hf₃ : Injective f₃ := Subgroup.inclusion_injective _
  exact ⟨f₃.comp f₂, hf₃.comp hf₂⟩

end TileSet

namespace Protoset

variable (ιₜ) {H : Subgroup G}

/-- Whether `ps` is weakly aperiodic (for `TileSet ps ιₜ` that satisfy the property `p`); that is,
whether it has such a `TileSet`, but none is strongly periodic. -/
def WeaklyAperiodic (p : TileSetFunction ps Prop H) : Prop :=
  (∃ t : TileSet ps ιₜ, p t) ∧ ∀ t : TileSet ps ιₜ, p t → ¬ t.StronglyPeriodic

/-- Whether `ps` is strongly aperiodic (for `TileSet ps ιₜ` that satisfy the property `p`); that
is, whether it has such a `TileSet`, but none is weakly periodic. -/
def StronglyAperiodic (p : TileSetFunction ps Prop H) : Prop :=
  (∃ t : TileSet ps ιₜ, p t) ∧ ∀ t : TileSet ps ιₜ, p t → ¬ t.WeaklyPeriodic 1

variable {ιₜ}

lemma WeaklyAperiodic.aleph0_le_isohedralNumber {p : TileSetFunction ps Prop H}
    (h : ps.WeaklyAperiodic ιₜ p) (hf : ∀ i, (ps i : Set X).Finite)
    (hu : ∀ t : TileSet ps ιₜ, p t → t.UnionEqUniv) : ℵ₀ ≤ ps.isohedralNumber ιₜ p := by
  rw [le_isohedralNumber_iff Cardinal.aleph0_ne_zero]
  rcases h with ⟨he, hnp⟩
  refine ⟨he, fun t hpt ↦ ?_⟩
  by_contra hi
  rw [not_le] at hi
  refine hnp t hpt (TileSet.stronglyPeriodic_of_isohedralNumber_lt_aleph0 hi
    (t.finite_apply_of_forall_finite hf) (hu t hpt))

lemma weaklyAperiodic_of_aleph0_le_isohedralNumber {p : TileSetFunction ps Prop H}
    (h : ℵ₀ ≤ ps.isohedralNumber ιₜ p)
    (hf : ∀ t : TileSet ps ιₜ, p t → t.FiniteDistinctIntersections)
    (hn : ∀ i, (ps i : Set X).Nonempty) : ps.WeaklyAperiodic ιₜ p := by
  rw [le_isohedralNumber_iff Cardinal.aleph0_ne_zero] at h
  rcases h with ⟨he, hnp⟩
  refine ⟨he, fun t hpt hp ↦ ?_⟩
  have hi := hnp t hpt
  revert hi
  rw [← Not, not_le]
  refine TileSet.StronglyPeriodic.isohedralNumber_lt_aleph0 hp (hf t hpt)
    (t.nonempty_apply_of_forall_nonempty hn)

lemma weaklyAperiodic_iff_aleph0_le_isohedralNumber {p : TileSetFunction ps Prop H}
    (ht : ∀ t : TileSet ps ιₜ, p t → t.IsTiling) (hf : ∀ i, (ps i : Set X).Finite)
    (hn : ∀ i, (ps i : Set X).Nonempty) : ps.WeaklyAperiodic ιₜ p ↔ ℵ₀ ≤ ps.isohedralNumber ιₜ p :=
  ⟨fun h ↦ h.aleph0_le_isohedralNumber hf fun t hpt ↦ TileSet.IsTiling.unionEqUniv (ht t hpt),
   fun h ↦ weaklyAperiodic_of_aleph0_le_isohedralNumber h
     (fun t hpt ↦ TileSet.IsTiling.finiteDistinctIntersections (ht t hpt)) hn⟩

end Protoset

end Discrete

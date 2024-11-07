/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Combinatorics.Tiling.Function.Disjoint
import AM.Mathlib.Combinatorics.Tiling.Function.Union
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Isohedral numbers of tilings and protosets

This file defines the action of a tiling's symmetry group on the tiles of that tiling, and
isohedral numbers of tilings and protosets in a discrete context.

The isohedral number of a tiling is the number of orbits of tiles under the action of its
symmetry group.  We define this for an arbitrary `TileSet`.  The isohedral number of a protoset
(possibly with matching rules) is the minimum of the isohedral numbers of tilings by that
protoset (that satisfy those matching rules).

## Main definitions

* `t.isohedralNumber`: A `TileSetFunction` for the isohedral number of `t`, as a
`Cardinal`.

* `t.isohedralNumberNat`: A `TileSetFunction` for the isohedral number of `t`, as a
natural number.

* `Protoset.isohedralNumber`: The isohedral number of a protoset, as a `Cardinal`.

* `Protoset.isohedralNumberNat`: The isohedral number of a protoset, as a natural number.

## References

* Branko Grünbaum and G. C. Shephard, Tilings and Patterns, 1987
-/


noncomputable section

namespace Discrete

open Function
open scoped Cardinal Pointwise

variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}

namespace TileSet

instance (t : TileSet ps ιₜ) : MulAction t.symmetryGroup (t : Set (PlacedTile ps)) where
  smul := fun g pt ↦ ⟨(g : G) • ↑pt, smul_mem_of_mem_of_mem_symmetryGroup g.property pt.property⟩
  one_smul := fun pt ↦ by
    simp only [HSMul.hSMul, Subtype.ext_iff]
    exact one_smul _ _
  mul_smul := fun x y pt ↦ by
    simp only [HSMul.hSMul, Subtype.ext_iff]
    exact mul_smul _ _ _

lemma coe_symmetryGroup_smul (t : TileSet ps ιₜ) (g : t.symmetryGroup)
    (pt : (t : Set (PlacedTile ps))) : ((g • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) =
      g • (pt : PlacedTile ps) :=
  rfl

lemma mem_smul_symmetryGroup_iff {t : TileSet ps ιₜ} {g : t.symmetryGroup}
    {pt : (t : Set (PlacedTile ps))} {x : X} :
    x ∈ ((g • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) ↔ x ∈ g • (pt : PlacedTile ps) :=
  Iff.rfl

lemma smul_mem_smul_symmetryGroup_iff {t : TileSet ps ιₜ} (g : t.symmetryGroup)
    {pt : (t : Set (PlacedTile ps))} {x : X} :
    g • x ∈ ((g • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) ↔
      x ∈ (pt : PlacedTile ps) := by
  simp [mem_smul_symmetryGroup_iff, Subgroup.smul_def]

lemma mem_smul_symmetryGroup_iff_smul_inv_mem {t : TileSet ps ιₜ} (g : t.symmetryGroup)
    {pt : (t : Set (PlacedTile ps))} {x : X} :
    x ∈ ((g • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) ↔
      g⁻¹ • x ∈ (pt : PlacedTile ps) := by
  simp_rw [mem_smul_symmetryGroup_iff, Subgroup.smul_def, Subgroup.coe_inv,
           PlacedTile.mem_smul_iff_smul_inv_mem]

lemma mem_inv_smul_symmetryGroup_iff_smul_mem {t : TileSet ps ιₜ} (g : t.symmetryGroup)
    {pt : (t : Set (PlacedTile ps))} {x : X} :
    x ∈ ((g⁻¹ • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) ↔
      g • x ∈ (pt : PlacedTile ps) := by
  simp_rw [mem_smul_symmetryGroup_iff, Subgroup.smul_def, Subgroup.coe_inv,
           PlacedTile.mem_inv_smul_iff_smul_mem]

/-- An equivalence between the orbits of tiles in a `TileSet` acted on by a group element and the
orbits in the original `TileSet`. -/
def smulOrbitEquiv (g : G) (t : TileSet ps ιₜ) :
    MulAction.orbitRel.Quotient (g • t).symmetryGroup
      ((g • t : TileSet ps ιₜ) : Set (PlacedTile ps)) ≃
        MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps)) where
  toFun := fun pt ↦ Quotient.liftOn' pt
    (fun x ↦ ⟦⟨g⁻¹ • ↑x, mem_smul_iff_smul_inv_mem.1 x.property⟩⟧)
    (fun x y h ↦ by
      convert Quotient.eq''.2 ?_
      rw [MulAction.orbitRel_apply] at h ⊢
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff] at h
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff]
      rcases h with ⟨a, ha, haa⟩
      change a • (y : PlacedTile ps) = x at haa
      refine ⟨g⁻¹ * a * g, mem_symmetryGroup_smul_iff'.1 ha, ?_⟩
      change (g⁻¹ * a * g) • (g⁻¹ • (y : PlacedTile ps)) = g⁻¹ • ↑x
      simpa [mul_smul] using haa)
  invFun := fun pt ↦ Quotient.liftOn' pt
    (fun x ↦ ⟦⟨g • ↑x, (smul_mem_smul_iff g).2 x.property⟩⟧)
    (fun x y h ↦ by
      convert Quotient.eq''.2 ?_
      rw [MulAction.orbitRel_apply] at h ⊢
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff] at h
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff]
      rcases h with ⟨a, ha, haa⟩
      change a • (y : PlacedTile ps) = x at haa
      refine ⟨g * a * g⁻¹, (mem_symmetryGroup_smul_iff g).2 ha, ?_⟩
      change (g * a * g⁻¹) • (g • (y : PlacedTile ps)) = g • ↑x
      simpa [mul_smul] using haa)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'']
    convert rfl
    change (_ : PlacedTile ps) = g • (g⁻¹ • _)
    simp
  right_inv := by
    intro x
    induction x using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'']
    convert rfl
    change (_ : PlacedTile ps) = g⁻¹ • (g • _)
    simp

/-- The number of orbits of tiles under the action of the symmetry group of a `TileSet`. This
definition actually uses the set of tiles, but it does not matter if there are duplicate tiles
because duplicate tiles are always equivalent under the symmetry group when considered to act by
the combination of a group element and a permutation of the index type. -/
def isohedralNumber : TileSetFunction ps Cardinal ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦
    #(MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))),
  by
    refine fun {ιₜ ιₜ'} (f t) ↦
      Cardinal.eq.2 ⟨Quotient.congr (Equiv.setCongr (by simp)) fun x y ↦ ?_⟩
    simp_rw [MulAction.orbitRel_apply]
    simp only [MulAction.mem_orbit_iff, Subtype.exists, symmetryGroup_reindex,
               Equiv.setCongr_apply, Subtype.ext_iff]
    exact Iff.rfl,
  fun {ιₜ g} (t _) ↦ Cardinal.eq.2 ⟨smulOrbitEquiv g t⟩⟩

lemma isohedralNumber_eq_card (t : TileSet ps ιₜ) :
    t.isohedralNumber = #(MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) :=
  rfl

lemma isohedralNumber_le_one_iff {t : TileSet ps ιₜ} :
    t.isohedralNumber ≤ 1 ↔ MulAction.IsPretransitive t.symmetryGroup
    (t : Set (PlacedTile ps)) := by
  rw [isohedralNumber_eq_card, Cardinal.le_one_iff_subsingleton,
      MulAction.pretransitive_iff_subsingleton_quotient]

lemma isohedralNumber_ne_zero_iff (t : TileSet ps ιₜ) : t.isohedralNumber ≠ 0 ↔ Nonempty ιₜ := by
  rw [isohedralNumber_eq_card, Cardinal.mk_ne_zero_iff, nonempty_quotient_iff,
      Set.nonempty_coe_sort, coeSet_apply, Set.range_nonempty_iff_nonempty]

lemma isohedralNumber_eq_zero_iff (t : TileSet ps ιₜ) : t.isohedralNumber = 0 ↔ IsEmpty ιₜ := by
  rw [← not_iff_not, not_isEmpty_iff]
  exact t.isohedralNumber_ne_zero_iff

lemma isohedralNumber_eq_one_iff {t : TileSet ps ιₜ} :
    t.isohedralNumber = 1
      ↔ Nonempty ιₜ ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by
  refine ⟨fun h ↦ ⟨t.isohedralNumber_ne_zero_iff.1 ?_, isohedralNumber_le_one_iff.1 h.le⟩,
          fun ⟨hn, ht⟩ ↦ (le_antisymm
            (isohedralNumber_le_one_iff.2 ht)
            (Cardinal.one_le_iff_ne_zero.2 (t.isohedralNumber_ne_zero_iff.2 hn)))⟩
  simp [h]

lemma aleph0_le_isohedralNumber_iff {t : TileSet ps ιₜ} :
    ℵ₀ ≤ t.isohedralNumber ↔
      Infinite (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by
  rw [Cardinal.infinite_iff, isohedralNumber_eq_card]

lemma isohedralNumber_lt_aleph0_iff {t : TileSet ps ιₜ} :
    t.isohedralNumber < ℵ₀ ↔
      Finite (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by
  rw [isohedralNumber_eq_card, Cardinal.lt_aleph0_iff_finite]

/-- The number of orbits of tiles under the action of the symmetry group of a `TileSet`, as a
natural number; zero if infinite. -/
def isohedralNumberNat : TileSetFunction ps ℕ ⊤ := isohedralNumber.comp Cardinal.toNat

lemma isohedralNumberNat_eq_card (t : TileSet ps ιₜ) :
    t.isohedralNumberNat =
      Nat.card (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) :=
  rfl

lemma isohedralNumberNat_eq_one_iff {t : TileSet ps ιₜ} :
    t.isohedralNumberNat = 1
      ↔ Nonempty ιₜ ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by
  rw [← isohedralNumber_eq_one_iff]
  simp [isohedralNumberNat]

lemma isohedralNumberNat_eq_zero_iff {t : TileSet ps ιₜ} :
    t.isohedralNumberNat = 0 ↔ IsEmpty ιₜ ∨
      Infinite (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by
  simp [isohedralNumberNat, isohedralNumber_eq_zero_iff, aleph0_le_isohedralNumber_iff]

/-- The symmetry group also acts on pairs of a tile and a point in that tile. -/
def subMulActionTilePoint (t : TileSet ps ιₜ) :
    SubMulAction t.symmetryGroup (Prod (t : Set (PlacedTile ps)) X) where
  carrier := {x | x.2 ∈ (x.1 : PlacedTile ps)}
  smul_mem' := fun g x h ↦ by
    rcases x with ⟨pt, x⟩
    simp only [Prod.smul_mk, Set.mem_setOf_eq, coe_symmetryGroup_smul, Subgroup.smul_def] at h ⊢
    exact (PlacedTile.smul_mem_smul_iff ↑g).2 h

instance (t : TileSet ps ιₜ) : MulAction t.symmetryGroup
    {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)} :=
  SubMulAction.SMulMemClass.toMulAction (S' := subMulActionTilePoint t)

lemma coe_smul_tilePoint {t : TileSet ps ιₜ} (g : t.symmetryGroup)
    (x : {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) :
    ((g • x : {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) : Prod _ _) =
      g • (x : Prod (t : Set (PlacedTile ps)) X) :=
  rfl

/-- Map from the quotient by the action of the symmetry group on pairs of a tile and a point in
that tile to the quotient by the action on tiles. -/
def quotientPlacedTileOfquotientTilePoint (t : TileSet ps ιₜ) :
    MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)} →
        MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps)) :=
  Subtype.val ∘
  Setoid.comapQuotientEquiv _ _ ∘
  Quot.mapRight (MulAction.orbitRel_le_fst _ _ _) ∘
  Subtype.val ∘
  Setoid.comapQuotientEquiv _ _ ∘
  (Quotient.congrRight <| Setoid.ext_iff.1 <|
    SubMulAction.orbitRel_of_subMul t.subMulActionTilePoint)

/-- Map from the quotient by the action of the symmetry group on pairs of a tile and a point in
that tile to the quotient by the action on points. -/
def quotientPointOfquotientTilePoint (t : TileSet ps ιₜ) :
    MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)} →
        MulAction.orbitRel.Quotient t.symmetryGroup X :=
  Subtype.val ∘
  Setoid.comapQuotientEquiv _ _ ∘
  Quot.mapRight (MulAction.orbitRel_le_snd _ _ _) ∘
  Subtype.val ∘
  Setoid.comapQuotientEquiv _ _ ∘
  (Quotient.congrRight <| Setoid.ext_iff.1 <|
    SubMulAction.orbitRel_of_subMul t.subMulActionTilePoint)

@[simp] lemma quotientPlacedTileOfquotientTilePoint_apply_mk {t : TileSet ps ιₜ}
    (x : {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) :
    t.quotientPlacedTileOfquotientTilePoint ⟦x⟧ = ⟦(Subtype.val x).1⟧ :=
  rfl

@[simp] lemma quotientPointOfquotientTilePoint_apply_mk {t : TileSet ps ιₜ}
    (x : {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) :
      t.quotientPointOfquotientTilePoint ⟦x⟧ = ⟦(Subtype.val x).2⟧ :=
  rfl

lemma surjective_quotientPlacedTileOfquotientTilePoint {t : TileSet ps ιₜ}
    (h : ∀ i, (t i : Set X).Nonempty) :
    Surjective t.quotientPlacedTileOfquotientTilePoint := by
  intro x
  induction' x using Quotient.inductionOn' with pt
  rcases pt with ⟨pt, i, rfl⟩
  obtain ⟨x, hx⟩ := h i
  exact ⟨⟦⟨(⟨t i, apply_mem _ _⟩, x), hx⟩⟧, rfl⟩

lemma surjective_quotientPointOfquotientTilePoint {t : TileSet ps ιₜ} (h : t.UnionEqUniv) :
    Surjective t.quotientPointOfquotientTilePoint := by
  intro x
  induction' x using Quotient.inductionOn' with p
  obtain ⟨pt, hpt, hp⟩ := UnionEqUniv.exists_mem_mem h p
  exact ⟨⟦⟨(⟨pt, hpt⟩, p), hp⟩⟧, rfl⟩

lemma preimage_quotientPlacedTileOfquotientTilePoint_eq_range {t : TileSet ps ιₜ}
    (pt : (t : Set (PlacedTile ps))) : t.quotientPlacedTileOfquotientTilePoint ⁻¹' {⟦pt⟧} =
      Set.range (fun x : {x // x ∈ (pt : PlacedTile ps)} ↦ ⟦⟨(pt, x), x.property⟩⟧) := by
  refine Set.Subset.antisymm (fun x h ↦ ?_) (Set.range_subset_iff.2 fun x ↦ (Set.mem_singleton _))
  rw [Set.mem_preimage] at h
  induction' x using Quotient.inductionOn' with pt'
  rcases pt' with ⟨⟨pt', x⟩, hx⟩
  simp only [Quotient.mk''_eq_mk, quotientPlacedTileOfquotientTilePoint_apply_mk,
             Set.mem_singleton_iff] at h
  rw [← @Quotient.mk''_eq_mk, Quotient.eq''] at h
  rcases h with ⟨g, rfl⟩
  dsimp only at hx
  rw [mem_smul_symmetryGroup_iff_smul_inv_mem] at hx
  refine ⟨⟨g⁻¹ • x, hx⟩, ?_⟩
  simp only
  rw [← @Quotient.mk''_eq_mk, Quotient.eq'', MulAction.orbitRel_apply]
  refine ⟨g⁻¹, Subtype.ext_iff.2 ?_⟩
  simp [coe_smul_tilePoint]

lemma preimage_quotientPointOfquotientTilePoint_eq_range {t : TileSet ps ιₜ} (x : X) :
    t.quotientPointOfquotientTilePoint ⁻¹' {⟦x⟧} =
      Set.range (fun pt : {pt // pt ∈ t ∧ x ∈ pt} ↦
        ⟦⟨(⟨pt, pt.property.1⟩, x), pt.property.2⟩⟧) := by
  refine Set.Subset.antisymm (fun y h ↦ ?_) (Set.range_subset_iff.2 fun y ↦ (Set.mem_singleton _))
  rw [Set.mem_preimage] at h
  induction' y using Quotient.inductionOn' with pt'
  rcases pt' with ⟨⟨pt', y⟩, hy⟩
  simp only [Quotient.mk''_eq_mk, quotientPointOfquotientTilePoint_apply_mk,
             Set.mem_singleton_iff] at h
  rw [← @Quotient.mk''_eq_mk, Quotient.eq''] at h
  rcases h with ⟨g, rfl⟩
  dsimp only at hy
  rw [← mem_inv_smul_symmetryGroup_iff_smul_mem] at hy
  refine ⟨⟨(g⁻¹ • pt' : (t : Set (PlacedTile ps))),
           (g⁻¹ • pt' : (t : Set (PlacedTile ps))).property, hy⟩, ?_⟩
  simp only
  rw [← @Quotient.mk''_eq_mk, Quotient.eq'', MulAction.orbitRel_apply]
  refine ⟨g⁻¹, Subtype.ext_iff.2 ?_⟩
  simp [coe_smul_tilePoint]

lemma finite_preimage_quotientPlacedTileOfquotientTilePoint {t : TileSet ps ιₜ}
    {pt : (t : Set (PlacedTile ps))} (h : ((pt : PlacedTile ps) : Set X).Finite) :
    (t.quotientPlacedTileOfquotientTilePoint ⁻¹' {⟦pt⟧}).Finite := by
  have := h.to_subtype
  rw [preimage_quotientPlacedTileOfquotientTilePoint_eq_range]
  exact Set.finite_range _

lemma finite_preimage_quotientPointOfquotientTilePoint {t : TileSet ps ιₜ} (x : X)
    (h : t.FiniteDistinctIntersectionsOn {x}) :
    (t.quotientPointOfquotientTilePoint ⁻¹' {⟦x⟧}).Finite := by
  have hf := (h x (Set.mem_singleton _)).to_subtype
  rw [Set.coe_setOf] at hf
  rw [preimage_quotientPointOfquotientTilePoint_eq_range]
  exact Set.finite_range _

lemma finite_quotient_tilePoint_of_isohedralNumber_lt_aleph0 {t : TileSet ps ιₜ}
    (h : t.isohedralNumber < ℵ₀) (hf : ∀ i, (t i : Set X).Finite) :
    Finite (MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) := by
  rw [← Set.finite_univ_iff, ← Set.preimage_univ (f := t.quotientPlacedTileOfquotientTilePoint),
      ← Set.biUnion_preimage_singleton]
  rw [isohedralNumber_lt_aleph0_iff] at h
  refine Finite.Set.finite_biUnion _ _ fun pt _ ↦ ?_
  induction' pt using Quotient.inductionOn' with pt
  rw [@Quotient.mk''_eq_mk]
  refine finite_preimage_quotientPlacedTileOfquotientTilePoint ?_
  rcases pt with ⟨pt, i, rfl⟩
  exact hf i

lemma isohedralNumber_lt_aleph0_of_finite_quotient_tilePoint {t : TileSet ps ιₜ}
    (hf : Finite (MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}))
    (hn : ∀ i, (t i : Set X).Nonempty) : t.isohedralNumber < ℵ₀ := by
  rw [isohedralNumber_lt_aleph0_iff]
  rw [← Set.finite_univ_iff] at hf ⊢
  exact Set.Finite.of_surjOn t.quotientPlacedTileOfquotientTilePoint
    (Set.surjective_iff_surjOn_univ.1 (surjective_quotientPlacedTileOfquotientTilePoint hn)) hf

end TileSet

namespace Protoset

variable (ιₜ) {H : Subgroup G}

/-- The minimum number of orbits of tiles in any `TileSet ps ιₜ` that satisfies the property `p`. -/
def isohedralNumber (p : TileSetFunction ps Prop H) : Cardinal :=
  ⨅ (t : {x : TileSet ps ιₜ // p x}), TileSet.isohedralNumber (t : TileSet ps ιₜ)

variable {ιₜ}

lemma isohedralNumber_eq_zero_iff {p : TileSetFunction ps Prop H} :
    isohedralNumber ιₜ p = 0 ↔ IsEmpty ιₜ ∨ ∀ t : TileSet ps ιₜ, ¬ p t := by
  simp_rw [isohedralNumber, Cardinal.iInf_eq_zero_iff, TileSet.isohedralNumber_eq_zero_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with h | ⟨⟨_, _⟩, hi⟩
    · exact Or.inr ((isEmpty_subtype _).1 h)
    · exact Or.inl hi
  · rcases h with h | h
    · simp only [isEmpty_subtype, h, Subtype.exists, exists_prop, and_true]
      rw [← not_exists]
      exact (Classical.em _).symm
    · simp [h]

lemma isohedralNumber_ne_zero_iff {p : TileSetFunction ps Prop H} :
    isohedralNumber ιₜ p ≠ 0 ↔ Nonempty ιₜ ∧ ∃ t : TileSet ps ιₜ, p t := by
  simp [isohedralNumber_eq_zero_iff, not_or]

lemma le_isohedralNumber_iff {p : TileSetFunction ps Prop H} {c : Cardinal} (h : c ≠ 0) :
    c ≤ isohedralNumber ιₜ p ↔
      (∃ t : TileSet ps ιₜ, p t) ∧ ∀ t : TileSet ps ιₜ, p t → c ≤ t.isohedralNumber := by
  rw [isohedralNumber]
  by_cases he : ∃ t : TileSet ps ιₜ, p t
  · simp only [he, true_and]
    rcases he with ⟨xt, hpxt⟩
    have : Nonempty {t : TileSet ps ιₜ // p t} := ⟨xt, hpxt⟩
    rw [le_ciInf_iff']
    exact ⟨fun h ↦ fun t ht ↦ h ⟨t, ht⟩, fun h ⟨t, ht⟩ ↦ h t ht⟩
  · simp only [not_exists] at he
    simp only [he, exists_false, IsEmpty.forall_iff, implies_true, and_true, iff_false, not_le,
               iInf]
    rw [← pos_iff_ne_zero] at h
    convert h
    convert Cardinal.sInf_empty
    simpa using he

lemma isohedralNumber_eq_one_iff {p : TileSetFunction ps Prop H} :
    isohedralNumber ιₜ p = 1 ↔ Nonempty ιₜ ∧ ∃ t : TileSet ps ιₜ, p t
      ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by
  rw [isohedralNumber, iInf]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Set.eq_empty_or_nonempty (Set.range fun (t : {x : TileSet ps ιₜ // p x}) ↦
      TileSet.isohedralNumber (t : TileSet ps ιₜ)) with he | hn
    · simp [he] at h
    · have h' := csInf_mem hn
      simp only [h, Set.mem_range, Subtype.exists, exists_prop,
                 TileSet.isohedralNumber_eq_one_iff] at h'
      rcases h' with ⟨t, hp, hni, hm⟩
      exact ⟨hni, t, hp, hm⟩
  · rcases h with ⟨hn, t, hp, ht⟩
    have hi := TileSet.isohedralNumber_eq_one_iff.2 ⟨hn, ht⟩
    refine IsLeast.csInf_eq ⟨?_, ?_⟩
    · change TileSet.isohedralNumber
        ((⟨t, hp⟩ : {x : TileSet ps ιₜ // p x}) : TileSet ps ιₜ) = 1 at hi
      rw [← hi]
      exact Set.mem_range_self _
    · intro c
      rw [Set.mem_range, Cardinal.one_le_iff_ne_zero]
      rintro ⟨t', rfl⟩
      rwa [TileSet.isohedralNumber_ne_zero_iff]

variable (ιₜ)

/-- The minimum number of orbits of tiles in any `TileSet ps ιₜ` that satisfies the property `p`,
as a natural number; zero if infinite or if no such `TileSet` exists. -/
def isohedralNumberNat (p : TileSetFunction ps Prop H) : ℕ :=
  Cardinal.toNat <| isohedralNumber ιₜ p

variable {ιₜ}

lemma isohedralNumberNat_eq_one_iff {p : TileSetFunction ps Prop H} :
    isohedralNumberNat ιₜ p = 1 ↔ Nonempty ιₜ ∧ ∃ t : TileSet ps ιₜ, p t
      ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by
  rw [← isohedralNumber_eq_one_iff]
  simp [isohedralNumberNat]

end Protoset

end Discrete

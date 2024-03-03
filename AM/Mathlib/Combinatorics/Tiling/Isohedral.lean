/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Combinatorics.Tiling.Basic
import AM.Mathlib.SetTheory.Cardinal.Basic

/-!
# Isohedral numbers of tilings and protosets

This file defines the action of a tiling's symmetry group on the tiles of that tiling, and
isohedral numbers of tilings and protosets in a discrete context.

The isohedral number of a tiling is the number of orbits of tiles under the action of its
symmetry group.  We define this for an arbitrary `TileSet`.  The isohedral number of a protoset
(possibly with matching rules) is the minimum of the isohedral numbers of tilings by that
protoset (that satisfy those matching rules).

## Main definitions

* `TileSet.isohedralNumber t`: A `TileSetFunction` for the isohedral number of `t`, as a
`Cardinal`.

* `TileSet.isohedralNumberNat t`: A `TileSetFunction` for the isohedral number of `t`, as a
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

variable {G X ιₚ ιₜ ιₜ' : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}

namespace TileSet

instance (t : TileSet ps ιₜ) : MulAction t.symmetryGroup (t : Set (PlacedTile ps)) where
  smul := fun g pt ↦ ⟨(g : G) • ↑pt, smul_mem_of_mem_of_mem_symmetryGroup g.property pt.property⟩
  one_smul := fun pt ↦ by
    simp only [HSMul.hSMul, Subtype.ext_iff]
    exact one_smul _ _
  mul_smul := fun x y pt ↦ by
    simp only [HSMul.hSMul, Subtype.ext_iff]
    exact mul_smul _ _ _

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
      change _ ∈ MulAction.orbit _ _ at h
      change _ ∈ MulAction.orbit _ _
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
      change _ ∈ MulAction.orbit _ _ at h
      change _ ∈ MulAction.orbit _ _
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
    convert Quotient.liftOn'_mk _ _ _
    change (_ : PlacedTile ps) = g • (g⁻¹ • _)
    simp
  right_inv := by
    intro x
    induction x using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'']
    convert Quotient.liftOn'_mk _ _ _
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
    change _ ∈ MulAction.orbit _ _ ↔ _ ∈ MulAction.orbit _ _
    simp only [MulAction.mem_orbit_iff, Subtype.exists, symmetryGroup_reindex,
               Equiv.setCongr_apply, Subtype.ext_iff]
    exact Iff.rfl,
  fun {ιₜ g} (t _) ↦ Cardinal.eq.2 ⟨smulOrbitEquiv g t⟩⟩

lemma isohedralNumber_eq_card (t : TileSet ps ιₜ) :
    isohedralNumber t = #(MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) :=
  rfl

lemma isohedralNumber_le_one_iff {t : TileSet ps ιₜ} :
    isohedralNumber t ≤ 1 ↔ MulAction.IsPretransitive t.symmetryGroup
    (t : Set (PlacedTile ps)) := by
  rw [isohedralNumber_eq_card, Cardinal.le_one_iff_subsingleton,
      MulAction.pretransitive_iff_subsingleton_quotient]

lemma isohedralNumber_ne_zero_iff (t : TileSet ps ιₜ) : isohedralNumber t ≠ 0 ↔ Nonempty ιₜ := by
  rw [isohedralNumber_eq_card, Cardinal.mk_ne_zero_iff, nonempty_quotient_iff,
      Set.nonempty_coe_sort, coeSet_apply, Set.range_nonempty_iff_nonempty]

lemma isohedralNumber_eq_zero_iff (t : TileSet ps ιₜ) : isohedralNumber t = 0 ↔ IsEmpty ιₜ := by
  rw [← not_iff_not, not_isEmpty_iff]
  exact t.isohedralNumber_ne_zero_iff

lemma isohedralNumber_eq_one_iff {t : TileSet ps ιₜ} :
    isohedralNumber t = 1
      ↔ Nonempty ιₜ ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by
  refine ⟨fun h ↦ ⟨t.isohedralNumber_ne_zero_iff.1 ?_, isohedralNumber_le_one_iff.1 h.le⟩,
          fun ⟨hn, ht⟩ ↦ (le_antisymm
            (isohedralNumber_le_one_iff.2 ht)
            (Cardinal.one_le_iff_ne_zero.2 (t.isohedralNumber_ne_zero_iff.2 hn)))⟩
  simp [h]

lemma aleph0_le_isohedralNumber_iff {t : TileSet ps ιₜ} :
    ℵ₀ ≤ isohedralNumber t ↔
      Infinite (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by
  rw [Cardinal.infinite_iff, isohedralNumber_eq_card]

/-- The number of orbits of tiles under the action of the symmetry group of a `TileSet`, as a
natural number; zero if infinite. -/
def isohedralNumberNat : TileSetFunction ps ℕ ⊤ := isohedralNumber.comp Cardinal.toNat

lemma isohedralNumberNat_eq_card (t : TileSet ps ιₜ) :
    isohedralNumberNat t =
      Nat.card (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) :=
  rfl

lemma isohedralNumberNat_eq_one_iff {t : TileSet ps ιₜ} :
    isohedralNumberNat t = 1
      ↔ Nonempty ιₜ ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by
  rw [← isohedralNumber_eq_one_iff]
  simp [isohedralNumberNat]

lemma isohedralNumberNat_eq_zero_iff {t : TileSet ps ιₜ} :
    isohedralNumberNat t = 0 ↔ IsEmpty ιₜ ∨
      Infinite (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by
  simp [isohedralNumberNat, isohedralNumber_eq_zero_iff, aleph0_le_isohedralNumber_iff]

end TileSet

namespace Protoset

variable (ιₜ) {s : Subgroup G}

/-- The minimum number of orbits of tiles in any `TileSet ps ιₜ` that satisfies the property `p`. -/
def isohedralNumber (p : TileSetFunction ps Prop s) : Cardinal :=
  ⨅ (t : {x : TileSet ps ιₜ // p x}), TileSet.isohedralNumber (t : TileSet ps ιₜ)

variable {ιₜ}

lemma isohedralNumber_eq_zero_iff {p : TileSetFunction ps Prop s} :
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

lemma isohedralNumber_ne_zero_iff {p : TileSetFunction ps Prop s} :
    isohedralNumber ιₜ p ≠ 0 ↔ Nonempty ιₜ ∧ ∃ t : TileSet ps ιₜ, p t := by
  simp [isohedralNumber_eq_zero_iff, not_or]

lemma isohedralNumber_eq_one_iff {p : TileSetFunction ps Prop s} :
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
def isohedralNumberNat (p : TileSetFunction ps Prop s) : ℕ :=
  Cardinal.toNat <| isohedralNumber ιₜ p

variable {ιₜ}

lemma isohedralNumberNat_eq_one_iff {p : TileSetFunction ps Prop s} :
    isohedralNumberNat ιₜ p = 1 ↔ Nonempty ιₜ ∧ ∃ t : TileSet ps ιₜ, p t
      ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by
  rw [← isohedralNumber_eq_one_iff]
  simp [isohedralNumberNat]

end Protoset

end Discrete

/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Combinatorics.Tiling.Basic

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

## References

* Branko Grünbaum and G. C. Shephard, Tilings and Patterns, 1987
-/


noncomputable section

namespace Discrete

open Function
open scoped Cardinal Pointwise

variable {G X ιₚ ιₜ ιₜ' : Type*} [Group G] [MulAction G X] {p : Protoset G X ιₚ}

namespace TileSet

instance (t : TileSet p ιₜ) : MulAction t.symmetryGroup (t : Set (PlacedTile p)) where
  smul := fun g pt ↦ ⟨(g : G) • ↑pt, smul_mem_of_mem_of_mem_symmetryGroup g.property pt.property⟩
  one_smul := fun pt ↦ by
    simp only [HSMul.hSMul, Subtype.ext_iff]
    exact one_smul _ _
  mul_smul := fun x y pt ↦ by
    simp only [HSMul.hSMul, Subtype.ext_iff]
    exact mul_smul _ _ _

/-- An equivalence between the orbits of tiles in a `TileSet` acted on by a group element and the
orbits in the original `TileSet`. -/
def smulOrbitEquiv (g : G) (t : TileSet p ιₜ) :
    MulAction.orbitRel.Quotient (g • t).symmetryGroup
      ((g • t : TileSet p ιₜ) : Set (PlacedTile p)) ≃
        MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile p)) where
  toFun := fun pt ↦ Quotient.liftOn' pt
    (fun x ↦ ⟦⟨g⁻¹ • ↑x, mem_smul_iff_smul_inv_mem.1 x.property⟩⟧)
    (fun x y h ↦ by
      convert Quotient.eq''.2 ?_
      change _ ∈ MulAction.orbit _ _ at h
      change _ ∈ MulAction.orbit _ _
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff] at h
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff]
      rcases h with ⟨a, ha, haa⟩
      change a • (y : PlacedTile p) = x at haa
      refine ⟨g⁻¹ * a * g, mem_symmetryGroup_smul_iff'.1 ha, ?_⟩
      change (g⁻¹ * a * g) • (g⁻¹ • (y : PlacedTile p)) = g⁻¹ • ↑x
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
      change a • (y : PlacedTile p) = x at haa
      refine ⟨g * a * g⁻¹, (mem_symmetryGroup_smul_iff g).2 ha, ?_⟩
      change (g * a * g⁻¹) • (g • (y : PlacedTile p)) = g • ↑x
      simpa [mul_smul] using haa)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'']
    convert Quotient.liftOn'_mk _ _ _
    change (_ : PlacedTile p) = g • (g⁻¹ • _)
    simp
  right_inv := by
    intro x
    induction x using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'']
    convert Quotient.liftOn'_mk _ _ _
    change (_ : PlacedTile p) = g⁻¹ • (g • _)
    simp

/-- The number of orbits of tiles under the action of the symmetry group of a `TileSet`. This
definition actually uses the set of tiles, but it does not matter if there are duplicate tiles
because duplicate tiles are always equivalent under the symmetry group when considered to act by
the combination of a group element and a permutation of the index type. -/
def isohedralNumber : TileSetFunction p Cardinal ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet p ιₜ) ↦
    #(MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile p))),
  by
    refine fun {ιₜ ιₜ'} (f t) ↦
      Cardinal.eq.2 ⟨Quotient.congr (Equiv.setCongr (by simp)) fun x y ↦ ?_⟩
    change _ ∈ MulAction.orbit _ _ ↔ _ ∈ MulAction.orbit _ _
    simp only [MulAction.mem_orbit_iff, Subtype.exists, symmetryGroup_reindex,
               Equiv.setCongr_apply, Subtype.ext_iff]
    exact Iff.rfl,
  fun {ιₜ g} (t _) ↦ Cardinal.eq.2 ⟨smulOrbitEquiv g t⟩⟩

lemma isohedralNumber_eq_card (t : TileSet p ιₜ) :
    isohedralNumber t = #(MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile p))) :=
  rfl

/-- The number of orbits of tiles under the action of the symmetry group of a `TileSet`, as a
natural number; zero if infinite. -/
def isohedralNumberNat : TileSetFunction p ℕ ⊤ := isohedralNumber.comp Cardinal.toNat

lemma isohedralNumberNat_eq_card (t : TileSet p ιₜ) :
    isohedralNumberNat t =
      Nat.card (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile p))) :=
  rfl

end TileSet

end Discrete

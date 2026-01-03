/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Combinatorics.Tiling.Function.Disjoint
import AM.Mathlib.Combinatorics.Tiling.Function.Union

/-!
# Tilings

This file defines when tiles in a discrete context make a tiling of the whole space or part thereof.

## Main definitions

* `t.IsTilingOf s`: A `VarTileSetFunction` for whether `t` is a tiling of the set `s`.

* `t.IsTiling`: A `TileSetFunction` for whether `t` is a tiling of `X`.

## References

* [Branko Grünbaum and G. C. Shephard, *Tilings and Patterns*][GrunbaumShephard1987]
-/


noncomputable section

namespace Discrete

open Function
open scoped Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ : Type*}

namespace TileSet

/-- Whether `t` is a tiling of the set `s`. -/
def IsTilingOf : VarTileSetFunction (Set X) ps Prop ⊤ :=
  (TileSet.Disjoint.toVarTileSetFunction (Set X)).comp₂ UnionEq (· ∧ ·)

lemma isTilingOf_iff {t : TileSet ps ιₜ} {s : Set X} : t.IsTilingOf s ↔
    (Pairwise fun i j ↦ Disjoint (t i : Set X) (t j)) ∧ (⋃ i, (t i : Set X)) = s :=
  Iff.rfl

lemma isTilingOf_iff' {t : TileSet ps ιₜ} {s : Set X} : t.IsTilingOf s ↔
    t.Disjoint ∧ t.UnionEq s :=
  Iff.rfl

lemma IsTilingOf.disjoint {t : TileSet ps ιₜ} {s : Set X} (h : t.IsTilingOf s) :
    t.Disjoint :=
  And.left h

lemma IsTilingOf.unionEq {t : TileSet ps ιₜ} {s : Set X} (h : t.IsTilingOf s) :
    t.UnionEq s :=
  And.right h

lemma isTilingOf_iff_of_injective {t : TileSet ps ιₜ} {s : Set X} (h : Injective t) :
    t.IsTilingOf s ↔ ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ∧
      (⋃ pt ∈ t, (pt : Set X)) = s := by
  rw [isTilingOf_iff, ← TileSet.disjoint_iff, ← coeSet_disjoint_iff_disjoint_of_injective h,
    union_of_mem_eq_iUnion]

lemma isTilingOf_smul_set_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    t.IsTilingOf (g • s) ↔ (g⁻¹ • t).IsTilingOf s := by
  nth_rewrite 1 [← one_smul G t]
  rw [← mul_inv_cancel g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _

lemma isTilingOf_smul_tileSet_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    (g • t).IsTilingOf s ↔ t.IsTilingOf (g⁻¹ • s) := by
  nth_rewrite 2 [← one_smul G t]
  rw [← inv_mul_cancel g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _

@[simp] lemma isTilingOf_empty [IsEmpty ιₜ] (t : TileSet ps ιₜ) : t.IsTilingOf ∅ := by
  simp [isTilingOf_iff, Subsingleton.pairwise]

/-- Whether `t` is a tiling of the whole of `X`. -/
def IsTiling : TileSetFunction ps Prop ⊤ := TileSet.Disjoint.comp₂ (UnionEqUniv) (· ∧ ·)

lemma isTiling_iff {t : TileSet ps ιₜ} : t.IsTiling ↔
    (Pairwise fun i j ↦ Disjoint (t i : Set X) (t j)) ∧ (⋃ i, (t i : Set X)) = Set.univ :=
  Iff.rfl

lemma isTiling_iff' {t : TileSet ps ιₜ} : t.IsTiling ↔ t.Disjoint ∧ t.UnionEqUniv :=
  Iff.rfl

lemma isTiling_iff_of_injective {t : TileSet ps ιₜ} (h : Injective t) :
    t.IsTiling ↔ ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ∧
      (⋃ pt ∈ t, (pt : Set X)) = Set.univ := by
  rw [isTiling_iff, ← TileSet.disjoint_iff, ← coeSet_disjoint_iff_disjoint_of_injective h,
    union_of_mem_eq_iUnion]

lemma IsTiling.disjoint {t : TileSet ps ιₜ} (h : t.IsTiling) : t.Disjoint :=
  And.left h

lemma IsTiling.unionEqUniv {t : TileSet ps ιₜ} (h : t.IsTiling) : t.UnionEqUniv :=
  And.right h

lemma IsTilingOf.finiteIntersections {t : TileSet ps ιₜ} {s : Set X} (h : t.IsTilingOf s) :
    t.FiniteIntersections :=
  Disjoint.finiteIntersections (IsTilingOf.disjoint h)

lemma IsTiling.finiteIntersections {t : TileSet ps ιₜ} (h : t.IsTiling) :
    t.FiniteIntersections :=
  Disjoint.finiteIntersections (IsTiling.disjoint h)


lemma IsTilingOf.finiteDistinctIntersections {t : TileSet ps ιₜ} {s : Set X}
    (h : t.IsTilingOf s) : t.FiniteDistinctIntersections :=
  FiniteIntersections.finiteDistinctIntersections (IsTilingOf.finiteIntersections h)

lemma IsTiling.finiteDistinctIntersections {t : TileSet ps ιₜ}
    (h : t.IsTiling) : t.FiniteDistinctIntersections :=
  FiniteIntersections.finiteDistinctIntersections (IsTiling.finiteIntersections h)

end TileSet

end Discrete

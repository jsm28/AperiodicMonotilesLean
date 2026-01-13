/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Combinatorics.Tiling.Function.Basic
import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# Union properties for tiles

This file defines properties of unions of tiles in a discrete context.

## Main definitions

* `t.UnionEq s`: A `VarTileSetFunction` for whether the union of the tiles of `t` is the
set `s`.

* `t.UnionEqUniv`: A `TileSetFunction` for whether the union of the tiles of `t` is the
whole of `X`.

## References

* [Branko Grünbaum and G. C. Shephard, *Tilings and Patterns*][GrunbaumShephard1987]
-/


noncomputable section

namespace DiscreteTiling

open Function
open scoped Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' : Type*}

namespace TileSet

/-- Whether the union of the tiles of `t` is the set `s`. -/
def UnionEq : VarTileSetFunction (Set X) ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (s : Set X) (t : TileSet ps ιₜ) ↦ (⋃ i, (t i : Set X)) = s,
   by
     intro ιₜ ιₜ' f s t
     simp only [eq_iff_iff]
     convert Iff.rfl
     exact f.symm.iSup_comp.symm,
   by
     simp [TileSet.smul_apply, ← Set.smul_set_iUnion]⟩

lemma unionEq_iff {t : TileSet ps ιₜ} {s : Set X} : t.UnionEq s ↔ (⋃ i, (t i : Set X)) = s :=
  Iff.rfl

lemma unionEq_iff' {t : TileSet ps ιₜ} {s : Set X} :
    t.UnionEq s ↔ (⋃ pt ∈ t, (pt : Set X)) = s := by
  rw [unionEq_iff, union_of_mem_eq_iUnion]

@[simp] lemma UnionEq.exists_mem_iff {t : TileSet ps ιₜ} {s : Set X} (h : t.UnionEq s) {x : X} :
    (∃ i, x ∈ t i) ↔ x ∈ s := by
  rw [← unionEq_iff'.1 h]
  simp

lemma UnionEq.exists_mem_mem_iff {t : TileSet ps ιₜ} {s : Set X} (h : t.UnionEq s) {x : X} :
    (∃ pt ∈ t, x ∈ pt) ↔ x ∈ s := by
  rw [← unionEq_iff'.1 h]
  simp

@[simp] lemma unionEq_reindex_iff_of_surjective {t : TileSet ps ιₜ} {s : Set X} {e : ιₜ' → ιₜ}
    (h : Surjective e) : (t.reindex e).UnionEq s ↔ t.UnionEq s :=
  (h.iUnion_comp (fun i ↦ (t i : Set X))).congr_left

lemma unionEq_smul_set_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    t.UnionEq (g • s) ↔ (g⁻¹ • t).UnionEq s := by
  nth_rewrite 1 [← one_smul G t]
  rw [← mul_inv_cancel g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _

lemma unionEq_smul_tileSet_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    (g • t).UnionEq s ↔ t.UnionEq (g⁻¹ • s) := by
  nth_rewrite 2 [← one_smul G t]
  rw [← inv_mul_cancel g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _

@[simp] lemma unionEq_empty [IsEmpty ιₜ] (t : TileSet ps ιₜ) : t.UnionEq ∅ := by
  simp [unionEq_iff]

/-- Whether the union of the tiles of `t` is the whole of `X`. -/
def UnionEqUniv : TileSetFunction ps Prop ⊤ := (UnionEq.toTileSetFunction Set.univ).ofLE (by simp)

lemma unionEqUniv_iff {t : TileSet ps ιₜ} : t.UnionEqUniv ↔ (⋃ i, (t i : Set X)) = Set.univ :=
  Iff.rfl

lemma unionEqUniv_iff' {t : TileSet ps ιₜ} :
    t.UnionEqUniv ↔ (⋃ pt ∈ t, (pt : Set X)) = Set.univ := by
  rw [unionEqUniv_iff, union_of_mem_eq_iUnion]

lemma unionEqUniv_iff_unionEq {t : TileSet ps ιₜ} : t.UnionEqUniv ↔ t.UnionEq Set.univ :=
  Iff.rfl

lemma UnionEqUniv.exists_mem {t : TileSet ps ιₜ} (h : t.UnionEqUniv) (x : X) :
    ∃ i, x ∈ t i := by
  rw [unionEqUniv_iff_unionEq] at h
  rw [UnionEq.exists_mem_iff h]
  exact Set.mem_univ _

lemma UnionEqUniv.exists_mem_mem {t : TileSet ps ιₜ} (h : t.UnionEqUniv) (x : X) :
    ∃ pt ∈ t, x ∈ pt := by
  rw [unionEqUniv_iff_unionEq] at h
  rw [UnionEq.exists_mem_mem_iff h]
  exact Set.mem_univ _

@[simp] lemma unionEqUniv_reindex_iff_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (h : Surjective e) : (t.reindex e).UnionEqUniv ↔ t.UnionEqUniv :=
  unionEq_reindex_iff_of_surjective h

end TileSet

end DiscreteTiling

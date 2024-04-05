/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Combinatorics.Tiling.Function.Basic
import Mathlib.Logic.Equiv.Pairwise

/-!
# Disjointness properties for tiles

This file defines disjointness properties for tiles in a discrete context.

## Main definitions

* `TileSet.Disjoint t`: A `TileSetFunction` for whether the tiles of `t` are disjoint.

* `TileSet.Disjoint s t`: A `VarTileSetFunction` for whether the tiles of `t` are disjoint within
the set `s`.

* `TileSet.FiniteIntersections t`: A `TileSetFunction` for whether only finitely many of the
tiles of `t` contain any point.

* `TileSet.FiniteIntersectionsOn s t`: A `VarTileSetFunction` for whether only finitely many of
the tiles of `t` contain any point of `s`.

* `TileSet.FiniteDistinctIntersections t`: A `TileSetFunction` for whether only finitely many
distinct tiles of `t` contain any point.

* `TileSet.FiniteDistinctIntersectionsOn s t`: A `VarTileSetFunction` for whether only finitely
many distinct tiles of `t` contain any point of `s`.

## References

* Branko Grünbaum and G. C. Shephard, Tilings and Patterns, 1987
-/


noncomputable section

namespace Discrete

open Function
open scoped Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' F : Type*}
variable [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]

namespace TileSet

/-- Whether the tiles of `t` are pairwise disjoint. -/
protected def Disjoint : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ Pairwise fun i j ↦ Disjoint (t i : Set X) (t j),
   by
     intro ιₜ ιₜ' f t
     simp only [eq_iff_iff]
     convert EquivLike.pairwise_comp_iff f.symm _
     rfl,
   by simp [TileSet.smul_apply]⟩

protected lemma disjoint_iff {t : TileSet ps ιₜ} :
    TileSet.Disjoint t ↔ Pairwise fun i j ↦ Disjoint (t i : Set X) (t j) :=
  Iff.rfl

lemma Disjoint.reindex_of_injective {t : TileSet ps ιₜ} (hd : TileSet.Disjoint t) {e : ιₜ' → ιₜ}
    (h : Injective e) : TileSet.Disjoint (t.reindex e) :=
  hd.comp_of_injective h

lemma Disjoint.reindex_of_embeddingLike {t : TileSet ps ιₜ} (hd : TileSet.Disjoint t) (e : F) :
    TileSet.Disjoint (t.reindex e) :=
  EmbeddingLike.pairwise_comp e hd

lemma Disjoint.reindex_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hd : TileSet.Disjoint (t.reindex e)) (h : Surjective e) : TileSet.Disjoint t :=
  Pairwise.of_comp_of_surjective hd h

@[simp] lemma disjoint_of_subsingleton [Subsingleton ιₜ] (t : TileSet ps ιₜ) :
    TileSet.Disjoint t := by
  simp [TileSet.disjoint_iff, Subsingleton.pairwise]

lemma Disjoint.coeSet_disjoint {t : TileSet ps ιₜ} (hd : TileSet.Disjoint t) :
    (t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y :=
  hd.range_pairwise (r := fun (x y : PlacedTile ps) ↦ Disjoint (x : Set X) y)

lemma coeSet_disjoint_iff_disjoint_of_injective {t : TileSet ps ιₜ} (h : Injective t) :
    ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ↔ TileSet.Disjoint t :=
  ⟨fun hd ↦ hd.on_injective h Set.mem_range_self, Disjoint.coeSet_disjoint⟩

/-- Whether the tiles of `t` are pairwise disjoint within the set `s`. -/
protected def DisjointOn : VarTileSetFunction (Set X) ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (s : Set X) (t : TileSet ps ιₜ) ↦ Pairwise fun i j ↦
     Disjoint ((t i : Set X) ∩ s) ((t j : Set X) ∩ s),
   by
     intro ιₜ ιₜ' f s t
     simp only [eq_iff_iff]
     convert EquivLike.pairwise_comp_iff f.symm _
     rfl,
   by simp [TileSet.smul_apply, ← Set.smul_set_inter]⟩

protected lemma disjointOn_iff {s : Set X} {t : TileSet ps ιₜ} :
    TileSet.DisjointOn s t ↔ Pairwise fun i j ↦ Disjoint ((t i : Set X) ∩ s) ((t j : Set X) ∩ s) :=
  Iff.rfl

lemma DisjointOn.reindex_of_injective {s : Set X} {t : TileSet ps ιₜ} (hd : TileSet.DisjointOn s t)
    {e : ιₜ' → ιₜ} (h : Injective e) : TileSet.DisjointOn s (t.reindex e) :=
  hd.comp_of_injective h

lemma DisjointOn.reindex_of_embeddingLike {s : Set X} {t : TileSet ps ιₜ}
    (hd : TileSet.DisjointOn s t) (e : F) : TileSet.DisjointOn s (t.reindex e) :=
  EmbeddingLike.pairwise_comp e hd

lemma DisjointOn.reindex_of_surjective {s : Set X} {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hd : TileSet.DisjointOn s (t.reindex e)) (h : Surjective e) : TileSet.DisjointOn s t :=
  Pairwise.of_comp_of_surjective hd h

@[simp] lemma disjointOn_of_subsingleton [Subsingleton ιₜ] (s : Set X) (t : TileSet ps ιₜ) :
    TileSet.DisjointOn s t := by
  simp [TileSet.disjointOn_iff, Subsingleton.pairwise]

lemma Disjoint.disjointOn (s : Set X) {t : TileSet ps ιₜ} (hd : TileSet.Disjoint t) :
    TileSet.DisjointOn s t :=
  fun _ _ h ↦ ((hd h).inter_left _).inter_right _

/-- Whether only finitely many tiles of `t` contain any point. -/
def FiniteIntersections : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ ∀ x, {i | x ∈ t i}.Finite,
   by
     intro ιₜ ιₜ' f t
     refine forall_congr ?_
     simp only [eq_iff_iff]
     intro x
     convert Set.finite_image_iff (Set.injOn_of_injective (EquivLike.injective f) _)
     exact Equiv.setOf_apply_symm_eq_image_setOf f fun i ↦ x ∈ t i,
   by
     intro ιₜ g t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x ↦ by simpa using h (g • x), fun h ↦ fun x ↦ ?_⟩
     convert h (g⁻¹ • x) using 2
     ext i
     exact mem_smul_apply_iff_smul_inv_mem⟩

lemma finiteIntersections_iff {t : TileSet ps ιₜ} :
    FiniteIntersections t ↔ ∀ x, {i | x ∈ t i}.Finite :=
  Iff.rfl

lemma FiniteIntersections.reindex_of_injective {t : TileSet ps ιₜ}
    (hfi : FiniteIntersections t) {e : ιₜ' → ιₜ} (h : Injective e) :
    FiniteIntersections (t.reindex e) :=
  fun x ↦ Set.Finite.preimage (Set.injOn_of_injective h _) (hfi x)

lemma FiniteIntersections.reindex_of_embeddingLike {t : TileSet ps ιₜ}
    (hfi : FiniteIntersections t) (e : F) : FiniteIntersections (t.reindex e) :=
  FiniteIntersections.reindex_of_injective hfi (EmbeddingLike.injective _)

lemma FiniteIntersections.reindex_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : FiniteIntersections (t.reindex e)) (h : Surjective e) :
    FiniteIntersections t :=
  fun x ↦ Set.Finite.of_preimage (hfi x) h

@[simp] lemma finiteIntersections_of_subsingleton [Subsingleton ιₜ] (t : TileSet ps ιₜ) :
    FiniteIntersections t :=
  fun _ ↦ Set.subsingleton_of_subsingleton.finite

lemma Disjoint.finiteIntersections {t : TileSet ps ιₜ} (h : TileSet.Disjoint t) :
    FiniteIntersections t :=
  fun _ ↦ Set.Subsingleton.finite (subsingleton_setOf_mem_iff_pairwise_disjoint.2 h _)

/-- Whether only finitely many tiles of `t` contain any point of `s`. -/
def FiniteIntersectionsOn : VarTileSetFunction (Set X) ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (s : Set X) (t : TileSet ps ιₜ) ↦ ∀ x ∈ s, {i | x ∈ t i}.Finite,
   by
     intro ιₜ ιₜ' f s t
     simp only [eq_iff_iff]
     refine forall₂_congr (fun x _ ↦ ?_)
     convert Set.finite_image_iff (Set.injOn_of_injective (EquivLike.injective f) _)
     exact Equiv.setOf_apply_symm_eq_image_setOf f fun i ↦ x ∈ t i,
   by
     intro ιₜ g s t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x ↦ by simpa using h (g • x), fun h ↦ fun x hx ↦ ?_⟩
     convert h (g⁻¹ • x) (Set.mem_smul_set_iff_inv_smul_mem.1 hx) using 2
     ext i
     exact mem_smul_apply_iff_smul_inv_mem⟩

lemma finiteIntersectionsOn_iff {s : Set X} {t : TileSet ps ιₜ} :
    FiniteIntersectionsOn s t ↔ ∀ x ∈ s, {i | x ∈ t i}.Finite :=
  Iff.rfl

lemma FiniteIntersectionsOn.reindex_of_injective {s : Set X} {t : TileSet ps ιₜ}
    (hfi : FiniteIntersectionsOn s t) {e : ιₜ' → ιₜ} (h : Injective e) :
    FiniteIntersectionsOn s (t.reindex e) :=
  fun x hx ↦ Set.Finite.preimage (Set.injOn_of_injective h _) (hfi x hx)

lemma FiniteIntersectionsOn.reindex_of_embeddingLike {s : Set X} {t : TileSet ps ιₜ}
    (hfi : FiniteIntersectionsOn s t) (e : F) : FiniteIntersectionsOn s (t.reindex e) :=
  FiniteIntersectionsOn.reindex_of_injective hfi (EmbeddingLike.injective _)

lemma FiniteIntersectionsOn.reindex_of_surjective {s : Set X} {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : FiniteIntersectionsOn s (t.reindex e)) (h : Surjective e) :
    FiniteIntersectionsOn s t :=
  fun x hx ↦ Set.Finite.of_preimage (hfi x hx) h

@[simp] lemma finiteIntersectionsOn_of_subsingleton [Subsingleton ιₜ] (s : Set X)
    (t : TileSet ps ιₜ) : FiniteIntersectionsOn s t :=
  fun _ _ ↦ Set.subsingleton_of_subsingleton.finite

lemma DisjointOn.finiteIntersectionsOn {s : Set X} {t : TileSet ps ιₜ}
    (h : TileSet.DisjointOn s t) : FiniteIntersectionsOn s t := by
  refine fun x hx ↦ Set.Subsingleton.finite fun i hi j hj ↦ ?_
  by_contra hij
  have h' := h hij
  revert h'
  simp only [imp_false, Set.not_disjoint_iff]
  refine ⟨x, ?_⟩
  simp only [Set.mem_setOf_eq] at hi hj
  simp [hx, hi, hj]

lemma FiniteIntersections.finiteIntersectionsOn (s : Set X) {t : TileSet ps ιₜ}
    (hfi : FiniteIntersections t) : FiniteIntersectionsOn s t :=
  fun _ _ ↦ hfi _

/-- Whether only finitely many distinct tiles of `t` contain any point. -/
def FiniteDistinctIntersections : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ ∀ x, {pt | pt ∈ t ∧ x ∈ pt}.Finite,
   by simp,
   by
     intro ιₜ g t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x ↦ ?_, fun h ↦ fun x ↦ ?_⟩
     · convert h (g • x) using 0
       convert (Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g) _)).symm using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem,
             PlacedTile.mem_inv_smul_iff_smul_mem]
     · convert h (g⁻¹ • x) using 0
       convert Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g) _) using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem,
             PlacedTile.mem_inv_smul_iff_smul_mem]⟩

lemma finiteDistinctIntersections_iff {t : TileSet ps ιₜ} :
    FiniteDistinctIntersections t ↔ ∀ x, {pt | pt ∈ t ∧ x ∈ pt}.Finite :=
  Iff.rfl

lemma FiniteDistinctIntersections.reindex {t : TileSet ps ιₜ}
    (hfi : FiniteDistinctIntersections t) {e : ιₜ' → ιₜ} :
    FiniteDistinctIntersections (t.reindex e) := by
  refine fun x ↦ Set.Finite.subset (hfi x) ?_
  simp only [Set.setOf_subset_setOf, and_imp]
  exact fun _ h hx ↦ ⟨mem_of_mem_reindex h, hx⟩

lemma FiniteDistinctIntersections.reindex_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : FiniteDistinctIntersections (t.reindex e)) (h : Surjective e) :
    FiniteDistinctIntersections t := by
  intro x
  convert hfi x
  exact (mem_reindex_iff_of_surjective h).symm

lemma FiniteIntersections.finiteDistinctIntersections {t : TileSet ps ιₜ}
    (h : FiniteIntersections t) : FiniteDistinctIntersections t := by
  intro x
  convert Set.Finite.image t (h x)
  ext pt
  simp only [Set.mem_setOf_eq, Set.mem_image, TileSet.mem_def]
  refine ⟨fun ⟨⟨i, hi⟩, hx⟩ ↦ ?_, fun ⟨i, ⟨hx, hi⟩⟩ ↦ ?_⟩
  · subst hi
    exact ⟨i, hx, rfl⟩
  · subst hi
    exact ⟨⟨i, rfl⟩, hx⟩

@[simp] lemma finiteDistinctIntersections_of_subsingleton [Subsingleton ιₜ] (t : TileSet ps ιₜ) :
    FiniteDistinctIntersections t :=
  FiniteIntersections.finiteDistinctIntersections (finiteIntersections_of_subsingleton t)

lemma Disjoint.finiteDistinctIntersections {t : TileSet ps ιₜ}
    (h : TileSet.Disjoint t) : FiniteDistinctIntersections t :=
  FiniteIntersections.finiteDistinctIntersections (Disjoint.finiteIntersections h)

/-- Whether only finitely many distinct tiles of `t` contain any point of `s`. -/
def FiniteDistinctIntersectionsOn : VarTileSetFunction (Set X) ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (s : Set X) (t : TileSet ps ιₜ) ↦ ∀ x ∈ s, {pt | pt ∈ t ∧ x ∈ pt}.Finite,
   by simp,
   by
     intro ιₜ g s t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x hx ↦ ?_, fun h ↦ fun x hx ↦ ?_⟩
     · convert h (g • x) (by simp [hx]) using 0
       convert (Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g) _)).symm using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem,
             PlacedTile.mem_inv_smul_iff_smul_mem]
     · convert h (g⁻¹ • x) (Set.mem_smul_set_iff_inv_smul_mem.1 hx) using 0
       convert Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g) _) using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem,
             PlacedTile.mem_inv_smul_iff_smul_mem]⟩

lemma finiteDistinctIntersectionsOn_iff {s : Set X} {t : TileSet ps ιₜ} :
    FiniteDistinctIntersectionsOn s t ↔ ∀ x ∈ s, {pt | pt ∈ t ∧ x ∈ pt}.Finite :=
  Iff.rfl

lemma FiniteDistinctIntersectionsOn.reindex {s : Set X} {t : TileSet ps ιₜ}
    (hfi : FiniteDistinctIntersectionsOn s t) {e : ιₜ' → ιₜ} :
    FiniteDistinctIntersectionsOn s (t.reindex e) := by
  refine fun x hx ↦ Set.Finite.subset (hfi x hx) ?_
  simp only [Set.setOf_subset_setOf, and_imp]
  exact fun _ h hx ↦ ⟨mem_of_mem_reindex h, hx⟩

lemma FiniteDistinctIntersectionsOn.reindex_of_surjective {s : Set X} {t : TileSet ps ιₜ}
    {e : ιₜ' → ιₜ} (hfi : FiniteDistinctIntersectionsOn s (t.reindex e)) (h : Surjective e) :
    FiniteDistinctIntersectionsOn s t := by
  intro x
  convert hfi x
  exact (mem_reindex_iff_of_surjective h).symm

lemma FiniteIntersectionsOn.finiteDistinctIntersectionsOn {s : Set X} {t : TileSet ps ιₜ}
    (h : FiniteIntersectionsOn s t) : FiniteDistinctIntersectionsOn s t := by
  intro x hx
  convert Set.Finite.image t (h x hx)
  ext pt
  simp only [Set.mem_setOf_eq, Set.mem_image, TileSet.mem_def]
  refine ⟨fun ⟨⟨i, hi⟩, hx⟩ ↦ ?_, fun ⟨i, ⟨hx, hi⟩⟩ ↦ ?_⟩
  · subst hi
    exact ⟨i, hx, rfl⟩
  · subst hi
    exact ⟨⟨i, rfl⟩, hx⟩

@[simp] lemma finiteDistinctIntersectionsOn_of_subsingleton [Subsingleton ιₜ] (s : Set X)
    (t : TileSet ps ιₜ) : FiniteDistinctIntersectionsOn s t :=
  FiniteIntersectionsOn.finiteDistinctIntersectionsOn (finiteIntersectionsOn_of_subsingleton s t)

lemma DisjointOn.finiteDistinctIntersectionsOn {s : Set X} {t : TileSet ps ιₜ}
    (h : TileSet.DisjointOn s t) : FiniteDistinctIntersectionsOn s t :=
  FiniteIntersectionsOn.finiteDistinctIntersectionsOn (DisjointOn.finiteIntersectionsOn h)

lemma FiniteDistinctIntersections.finiteDistinctIntersectionsOn (s : Set X) {t : TileSet ps ιₜ}
    (hfi : FiniteDistinctIntersections t) : FiniteDistinctIntersectionsOn s t :=
  fun _ _ ↦ hfi _

end TileSet

end Discrete

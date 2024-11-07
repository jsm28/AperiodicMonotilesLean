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

* `t.Disjoint`: A `TileSetFunction` for whether the tiles of `t` are disjoint.

* `t.DisjointOn s`: A `VarTileSetFunction` for whether the tiles of `t` are disjoint
within the set `s`.

* `t.FiniteIntersections`: A `TileSetFunction` for whether only finitely many of the
tiles of `t` contain any point.

* `t.FiniteIntersectionsOn s`: A `VarTileSetFunction` for whether only finitely many of
the tiles of `t` contain any point of `s`.

* `t.FiniteDistinctIntersections`: A `TileSetFunction` for whether only finitely many
distinct tiles of `t` contain any point.

* `t.FiniteDistinctIntersectionsOn s`: A `VarTileSetFunction` for whether only finitely
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
    t.Disjoint ↔ Pairwise fun i j ↦ Disjoint (t i : Set X) (t j) :=
  Iff.rfl

lemma Disjoint.reindex_of_injective {t : TileSet ps ιₜ} (hd : t.Disjoint) {e : ιₜ' → ιₜ}
    (h : Injective e) : (t.reindex e).Disjoint :=
  hd.comp_of_injective h

lemma Disjoint.reindex_of_embeddingLike {t : TileSet ps ιₜ} (hd : t.Disjoint) (e : F) :
    (t.reindex e).Disjoint :=
  EmbeddingLike.pairwise_comp e hd

lemma Disjoint.reindex_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hd : (t.reindex e).Disjoint) (h : Surjective e) : t.Disjoint :=
  Pairwise.of_comp_of_surjective hd h

@[simp] lemma disjoint_of_subsingleton [Subsingleton ιₜ] (t : TileSet ps ιₜ) :
    t.Disjoint := by
  simp [TileSet.disjoint_iff, Subsingleton.pairwise]

lemma Disjoint.coeSet_disjoint {t : TileSet ps ιₜ} (hd : t.Disjoint) :
    (t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y :=
  hd.range_pairwise (r := fun (x y : PlacedTile ps) ↦ Disjoint (x : Set X) y)

lemma coeSet_disjoint_iff_disjoint_of_injective {t : TileSet ps ιₜ} (h : Injective t) :
    ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ↔ t.Disjoint :=
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
    t.DisjointOn s ↔ Pairwise fun i j ↦ Disjoint ((t i : Set X) ∩ s) ((t j : Set X) ∩ s) :=
  Iff.rfl

lemma DisjointOn.reindex_of_injective {s : Set X} {t : TileSet ps ιₜ} (hd : t.DisjointOn s)
    {e : ιₜ' → ιₜ} (h : Injective e) : (t.reindex e).DisjointOn s :=
  hd.comp_of_injective h

lemma DisjointOn.reindex_of_embeddingLike {s : Set X} {t : TileSet ps ιₜ}
    (hd : t.DisjointOn s) (e : F) : (t.reindex e).DisjointOn s :=
  EmbeddingLike.pairwise_comp e hd

lemma DisjointOn.reindex_of_surjective {s : Set X} {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hd : (t.reindex e).DisjointOn s) (h : Surjective e) : t.DisjointOn s :=
  Pairwise.of_comp_of_surjective hd h

@[simp] lemma disjointOn_of_subsingleton [Subsingleton ιₜ] (s : Set X) (t : TileSet ps ιₜ) :
    t.DisjointOn s := by
  simp [TileSet.disjointOn_iff, Subsingleton.pairwise]

lemma DisjointOn.subset {s₁ s₂ : Set X} {t : TileSet ps ιₜ} (hd : t.DisjointOn s₂)
    (hs : s₁ ⊆ s₂) : t.DisjointOn s₁ :=
  fun _ _ h ↦ Set.disjoint_of_subset (Set.inter_subset_inter_right _ hs)
    (Set.inter_subset_inter_right _ hs) (hd h)

@[simp] lemma disjointOn_empty (t : TileSet ps ιₜ) : t.DisjointOn ∅ := by
  simp [TileSet.DisjointOn, Pairwise]

@[simp] lemma disjointOn_univ_iff {t : TileSet ps ιₜ} :
    t.DisjointOn Set.univ ↔ t.Disjoint := by
  simp [TileSet.Disjoint, TileSet.DisjointOn]

lemma Disjoint.disjointOn (s : Set X) {t : TileSet ps ιₜ} (hd : t.Disjoint) :
    t.DisjointOn s :=
  fun _ _ h ↦ ((hd h).inter_left _).inter_right _

/-- Whether only finitely many tiles of `t` contain any point. -/
def FiniteIntersections : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ ∀ x, {i | x ∈ t i}.Finite,
   by
     intro ιₜ ιₜ' f t
     refine forall_congr ?_
     simp only [eq_iff_iff]
     intro x
     convert Set.finite_image_iff (Set.injOn_of_injective (EquivLike.injective f))
     exact Equiv.setOf_apply_symm_eq_image_setOf f fun i ↦ x ∈ t i,
   by
     intro ιₜ g t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x ↦ by simpa using h (g • x), fun h ↦ fun x ↦ ?_⟩
     convert h (g⁻¹ • x) using 2
     ext i
     exact mem_smul_apply_iff_smul_inv_mem⟩

lemma finiteIntersections_iff {t : TileSet ps ιₜ} :
    t.FiniteIntersections ↔ ∀ x, {i | x ∈ t i}.Finite :=
  Iff.rfl

lemma FiniteIntersections.reindex_of_injective {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersections) {e : ιₜ' → ιₜ} (h : Injective e) :
    (t.reindex e).FiniteIntersections :=
  fun x ↦ Set.Finite.preimage (Set.injOn_of_injective h) (hfi x)

lemma FiniteIntersections.reindex_of_embeddingLike {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersections) (e : F) : (t.reindex e).FiniteIntersections :=
  FiniteIntersections.reindex_of_injective hfi (EmbeddingLike.injective _)

lemma FiniteIntersections.reindex_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : (t.reindex e).FiniteIntersections) (h : Surjective e) :
    t.FiniteIntersections :=
  fun x ↦ Set.Finite.of_preimage (hfi x) h

@[simp] lemma finiteIntersections_of_subsingleton [Subsingleton ιₜ] (t : TileSet ps ιₜ) :
    t.FiniteIntersections :=
  fun _ ↦ Set.subsingleton_of_subsingleton.finite

lemma Disjoint.finiteIntersections {t : TileSet ps ιₜ} (h : t.Disjoint) :
    t.FiniteIntersections :=
  fun _ ↦ Set.Subsingleton.finite (subsingleton_setOf_mem_iff_pairwise_disjoint.2 h _)

/-- Whether only finitely many tiles of `t` contain any point of `s`. -/
def FiniteIntersectionsOn : VarTileSetFunction (Set X) ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (s : Set X) (t : TileSet ps ιₜ) ↦ ∀ x ∈ s, {i | x ∈ t i}.Finite,
   by
     intro ιₜ ιₜ' f s t
     simp only [eq_iff_iff]
     refine forall₂_congr (fun x _ ↦ ?_)
     convert Set.finite_image_iff (Set.injOn_of_injective (EquivLike.injective f))
     exact Equiv.setOf_apply_symm_eq_image_setOf f fun i ↦ x ∈ t i,
   by
     intro ιₜ g s t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x ↦ by simpa using h (g • x), fun h ↦ fun x hx ↦ ?_⟩
     convert h (g⁻¹ • x) (Set.mem_smul_set_iff_inv_smul_mem.1 hx) using 2
     ext i
     exact mem_smul_apply_iff_smul_inv_mem⟩

lemma finiteIntersectionsOn_iff {s : Set X} {t : TileSet ps ιₜ} :
    t.FiniteIntersectionsOn s ↔ ∀ x ∈ s, {i | x ∈ t i}.Finite :=
  Iff.rfl

lemma FiniteIntersectionsOn.reindex_of_injective {s : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersectionsOn s) {e : ιₜ' → ιₜ} (h : Injective e) :
    (t.reindex e).FiniteIntersectionsOn s :=
  fun x hx ↦ Set.Finite.preimage (Set.injOn_of_injective h) (hfi x hx)

lemma FiniteIntersectionsOn.reindex_of_embeddingLike {s : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersectionsOn s) (e : F) : (t.reindex e).FiniteIntersectionsOn s :=
  FiniteIntersectionsOn.reindex_of_injective hfi (EmbeddingLike.injective _)

lemma FiniteIntersectionsOn.reindex_of_surjective {s : Set X} {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : (t.reindex e).FiniteIntersectionsOn s) (h : Surjective e) :
    t.FiniteIntersectionsOn s :=
  fun x hx ↦ Set.Finite.of_preimage (hfi x hx) h

@[simp] lemma finiteIntersectionsOn_of_subsingleton [Subsingleton ιₜ] (s : Set X)
    (t : TileSet ps ιₜ) : t.FiniteIntersectionsOn s :=
  fun _ _ ↦ Set.subsingleton_of_subsingleton.finite

lemma FiniteIntersectionsOn.subset {s₁ s₂ : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersectionsOn s₂) (hs : s₁ ⊆ s₂) :
    t.FiniteIntersectionsOn s₁ :=
  fun x hx ↦ hfi x (Set.mem_of_mem_of_subset hx hs)

@[simp] lemma finiteIntersectionsOn_empty (t : TileSet ps ιₜ) :
    t.FiniteIntersectionsOn ∅ := by
  simp [TileSet.FiniteIntersectionsOn, Pairwise]

@[simp] lemma finiteIntersectionsOn_univ_iff {t : TileSet ps ιₜ} :
    t.FiniteIntersectionsOn Set.univ ↔ t.FiniteIntersections := by
  simp [TileSet.FiniteIntersections, TileSet.FiniteIntersectionsOn]

lemma DisjointOn.finiteIntersectionsOn {s : Set X} {t : TileSet ps ιₜ}
    (h : t.DisjointOn s) : t.FiniteIntersectionsOn s := by
  refine fun x hx ↦ Set.Subsingleton.finite fun i hi j hj ↦ ?_
  by_contra hij
  have h' := h hij
  revert h'
  simp only [imp_false, Set.not_disjoint_iff]
  refine ⟨x, ?_⟩
  simp only [Set.mem_setOf_eq] at hi hj
  simp [hx, hi, hj]

lemma FiniteIntersections.finiteIntersectionsOn (s : Set X) {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersections) : t.FiniteIntersectionsOn s :=
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
         (β := PlacedTile ps) g))).symm using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem,
             PlacedTile.mem_inv_smul_iff_smul_mem]
     · convert h (g⁻¹ • x) using 0
       convert Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g)) using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem,
             PlacedTile.mem_inv_smul_iff_smul_mem]⟩

lemma finiteDistinctIntersections_iff {t : TileSet ps ιₜ} :
    t.FiniteDistinctIntersections ↔ ∀ x, {pt | pt ∈ t ∧ x ∈ pt}.Finite :=
  Iff.rfl

lemma FiniteDistinctIntersections.reindex {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersections) {e : ιₜ' → ιₜ} :
    (t.reindex e).FiniteDistinctIntersections := by
  refine fun x ↦ Set.Finite.subset (hfi x) ?_
  simp only [Set.setOf_subset_setOf, and_imp]
  exact fun _ h hx ↦ ⟨mem_of_mem_reindex h, hx⟩

lemma FiniteDistinctIntersections.reindex_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : (t.reindex e).FiniteDistinctIntersections) (h : Surjective e) :
    t.FiniteDistinctIntersections := by
  intro x
  convert hfi x using 4
  exact (mem_reindex_iff_of_surjective h).symm

lemma FiniteIntersections.finiteDistinctIntersections {t : TileSet ps ιₜ}
    (h : t.FiniteIntersections) : t.FiniteDistinctIntersections := by
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
    t.FiniteDistinctIntersections :=
  FiniteIntersections.finiteDistinctIntersections (finiteIntersections_of_subsingleton t)

lemma Disjoint.finiteDistinctIntersections {t : TileSet ps ιₜ}
    (h : t.Disjoint) : t.FiniteDistinctIntersections :=
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
         (β := PlacedTile ps) g))).symm using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem,
             PlacedTile.mem_inv_smul_iff_smul_mem]
     · convert h (g⁻¹ • x) (Set.mem_smul_set_iff_inv_smul_mem.1 hx) using 0
       convert Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g)) using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem,
             PlacedTile.mem_inv_smul_iff_smul_mem]⟩

lemma finiteDistinctIntersectionsOn_iff {s : Set X} {t : TileSet ps ιₜ} :
    t.FiniteDistinctIntersectionsOn s ↔ ∀ x ∈ s, {pt | pt ∈ t ∧ x ∈ pt}.Finite :=
  Iff.rfl

lemma FiniteDistinctIntersectionsOn.reindex {s : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersectionsOn s) {e : ιₜ' → ιₜ} :
    (t.reindex e).FiniteDistinctIntersectionsOn s := by
  refine fun x hx ↦ Set.Finite.subset (hfi x hx) ?_
  simp only [Set.setOf_subset_setOf, and_imp]
  exact fun _ h hx ↦ ⟨mem_of_mem_reindex h, hx⟩

lemma FiniteDistinctIntersectionsOn.reindex_of_surjective {s : Set X} {t : TileSet ps ιₜ}
    {e : ιₜ' → ιₜ} (hfi : (t.reindex e).FiniteDistinctIntersectionsOn s) (h : Surjective e) :
    t.FiniteDistinctIntersectionsOn s := by
  intro x
  convert hfi x using 5
  exact (mem_reindex_iff_of_surjective h).symm

lemma FiniteIntersectionsOn.finiteDistinctIntersectionsOn {s : Set X} {t : TileSet ps ιₜ}
    (h : t.FiniteIntersectionsOn s) : t.FiniteDistinctIntersectionsOn s := by
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
    (t : TileSet ps ιₜ) : t.FiniteDistinctIntersectionsOn s :=
  FiniteIntersectionsOn.finiteDistinctIntersectionsOn (finiteIntersectionsOn_of_subsingleton s t)

lemma FiniteDistinctIntersectionsOn.subset {s₁ s₂ : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersectionsOn s₂) (hs : s₁ ⊆ s₂) :
    t.FiniteDistinctIntersectionsOn s₁ :=
  fun x hx ↦ hfi x (Set.mem_of_mem_of_subset hx hs)

@[simp] lemma finiteDistinctIntersectionsOn_empty (t : TileSet ps ιₜ) :
    t.FiniteDistinctIntersectionsOn ∅ := by
  simp [TileSet.FiniteDistinctIntersectionsOn, Pairwise]

@[simp] lemma finiteDistinctIntersectionsOn_univ_iff {t : TileSet ps ιₜ} :
    t.FiniteDistinctIntersectionsOn Set.univ ↔ t.FiniteDistinctIntersections := by
  simp [TileSet.FiniteDistinctIntersections, TileSet.FiniteDistinctIntersectionsOn]

lemma DisjointOn.finiteDistinctIntersectionsOn {s : Set X} {t : TileSet ps ιₜ}
    (h : t.DisjointOn s) : t.FiniteDistinctIntersectionsOn s :=
  FiniteIntersectionsOn.finiteDistinctIntersectionsOn (DisjointOn.finiteIntersectionsOn h)

lemma FiniteDistinctIntersections.finiteDistinctIntersectionsOn (s : Set X) {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersections) : t.FiniteDistinctIntersectionsOn s :=
  fun _ _ ↦ hfi _

end TileSet

end Discrete

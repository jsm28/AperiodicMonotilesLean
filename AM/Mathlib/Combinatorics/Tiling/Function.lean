/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Combinatorics.Tiling.TileSet
import AM.Mathlib.Data.Set.Pairwise.Basic
import AM.Mathlib.Logic.Equiv.Pairwise
import AM.Mathlib.Logic.Equiv.Set
import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# Bundled functions on tilings

This file defines bundled functions on tilings in a discrete context.

## Main definitions

* `TileSetFunction ps α s`: A bundled function from `TileSet ps ιₜ` to `α` that is invariant under
change or permutation of index type `ιₜ` and under the action of group elements in `s`.

* `TileSet.IsTilingOf s t`: A `TileSetFunction` for whether `t` is a tiling of the set `s` of
points.

* `TileSet.IsTiling t`: A `TileSetFunction` for whether `t` is a tiling of `X`.

## References

* Branko Grünbaum and G. C. Shephard, Tilings and Patterns, 1987
-/


noncomputable section

namespace Discrete

open Function
open scoped Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]

universe u
variable {ps : Protoset G X ιₚ} {ιᵤ ιᵤ' : Type u} {ιₜ ιₜ' Eᵤ F α β γ : Type*}
variable [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ] [EquivLike Eᵤ ιᵤ' ιᵤ]

section

variable (ps α) (s : Subgroup G)

/-- A `TileSetFunction ps α s` is a function from `TileSet ps ιₜ` to `α` that is invariant under
change or permutation of index type `ιₜ` (within the same universe) and under the action of group
elements in `s`. -/
@[ext] structure TileSetFunction where
  /-- The function.  Use the coercion to a function rather than using `toFun` directly. -/
  toFun : {ιₜ : Type u} → TileSet ps ιₜ → α
  /-- The function is invariant under reindexing. -/
  reindex_eq' : ∀ {ιₜ ιₜ' : Type u} (f : ιₜ ≃ ιₜ') (t : TileSet ps ιₜ),
    toFun (t.reindex f.symm) = toFun t
  /-- The function is invariant under the group action within the subgroup `s`. -/
  smul_eq : ∀ {ιₜ : Type u} {g : G} (t : TileSet ps ιₜ), g ∈ s → toFun (g • t) = toFun t

end

namespace TileSetFunction

variable (ps α) (s : Subgroup G)

instance : CoeFun (TileSetFunction ps α s) (fun _ ↦ {ιₜ : Type*} → TileSet ps ιₜ → α) where
  coe := toFun

attribute [coe] toFun

attribute [simp] smul_eq

variable {ps α s}

@[simp] lemma reindex_eq (f : TileSetFunction ps α s) (t : TileSet ps ιᵤ) (e : Eᵤ) :
    f (t.reindex e) = f t :=
  f.reindex_eq' (EquivLike.toEquiv e).symm t

@[simp] lemma reindex_eq_of_bijective (f : TileSetFunction ps α s) (t : TileSet ps ιᵤ)
    {e : ιᵤ' → ιᵤ} (h : Bijective e) : f (t.reindex e) = f t :=
  f.reindex_eq t <| Equiv.ofBijective e h

lemma coe_mk (f : {ιₜ : Type*} → TileSet ps ιₜ → α) (hr hs) :
    (⟨f, hr, hs⟩ : TileSetFunction ps α s) = @f :=
  rfl

lemma reindex_iff {f : TileSetFunction ps Prop s} {t : TileSet ps ιᵤ} (e : Eᵤ) :
    f (t.reindex e) ↔ f t :=
  by simp

lemma reindex_iff_of_bijective {f : TileSetFunction ps Prop s} {t : TileSet ps ιᵤ} {e : ιᵤ' → ιᵤ}
    (h : Bijective e) : f (t.reindex e) ↔ f t :=
  by simp [h]

lemma smul_iff {f : TileSetFunction ps Prop s} {g : G} {t : TileSet ps ιₜ} (hg : g ∈ s) :
    f (g • t) ↔ f t :=
  by simp [hg]

lemma eq_of_coeSet_eq_of_injective (f : TileSetFunction ps α s) {t₁ : TileSet ps ιᵤ}
    {t₂ : TileSet ps ιᵤ'} (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁)
    (h₂ : Injective t₂) : f t₁ = f t₂ := by
  rw [← TileSet.reindex_equivOfCoeSetEqOfInjective h h₁ h₂]
  exact (reindex_eq _ _ _).symm

lemma iff_of_coeSet_eq_of_injective (f : TileSetFunction ps Prop s) {t₁ : TileSet ps ιᵤ}
    {t₂ : TileSet ps ιᵤ'} (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁)
    (h₂ : Injective t₂) : f t₁ ↔ f t₂ := by
  simpa using f.eq_of_coeSet_eq_of_injective h h₁ h₂

variable (ps s)

/-- The constant `TileSetFunction`. -/
protected def const (y : α) : TileSetFunction ps α s :=
  ⟨fun {ιₜ} ↦ const (TileSet ps ιₜ) y, by simp, by simp⟩

@[simp] lemma const_apply (y : α) (t : TileSet ps ιₜ) : TileSetFunction.const ps s y t = y := rfl

variable {ps s}

instance [Nonempty α] : Nonempty (TileSetFunction ps α s) :=
  ⟨TileSetFunction.const ps s <| Classical.arbitrary _⟩

/-- Composing a `TileSetFunction` with a function on the result type. -/
protected def comp (f : TileSetFunction ps α s) (fyz : α → β) : TileSetFunction ps β s :=
  ⟨fyz ∘ f.toFun, by simp, fun _ hg ↦ by simp [hg]⟩

@[simp] lemma comp_apply (f : TileSetFunction ps α s) (fyz : α → β) (t : TileSet ps ιₜ) :
    f.comp fyz t = fyz (f t) :=
  rfl

/-- Combining two `TileSetFunction`s with a function on their result types. -/
protected def comp₂ (f : TileSetFunction ps α s) (f' : TileSetFunction ps β s) (fyz : α → β → γ) :
    TileSetFunction ps γ s :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ fyz (f t) (f' t), by simp, fun _ hg ↦ by simp [hg]⟩

@[simp] lemma comp₂_apply (f : TileSetFunction ps α s) (f' : TileSetFunction ps β s)
    (fyz : α → β → γ) (t : TileSet ps ιₜ) : f.comp₂ f' fyz t = fyz (f t) (f' t) :=
  rfl

/-- Converting a `TileSetFunction ps α s` to one using a subgroup of `s`. -/
protected def ofLE (f : TileSetFunction ps α s) {s' : Subgroup G} (h : s' ≤ s) :
    TileSetFunction ps α s' :=
  ⟨f.toFun, by simp, fun _ hg ↦ by simp [SetLike.le_def.1 h hg]⟩

@[simp] lemma ofLE_apply (f : TileSetFunction ps α s) {s' : Subgroup G} (h : s' ≤ s)
    (t : TileSet ps ιₜ) : f.ofLE h t = f t :=
  rfl

end TileSetFunction

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

/-- Whether the union of the tiles of `t` is the set `s`. -/
def UnionEq (s : Set X) : TileSetFunction ps Prop (MulAction.stabilizer G s) :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ (⋃ i, (t i : Set X)) = s,
   by
     intro ιₜ ιₜ' f t
     simp only [eq_iff_iff]
     convert Iff.rfl
     exact f.symm.iSup_comp.symm,
   by
     intro ιₜ g t hg
     rw [MulAction.mem_stabilizer_iff] at hg
     nth_rewrite 1 [← hg]
     simp [TileSet.smul_apply, ← Set.smul_set_iUnion]⟩

lemma unionEq_iff {t : TileSet ps ιₜ} {s : Set X} : UnionEq s t ↔ (⋃ i, (t i : Set X)) = s :=
  Iff.rfl

lemma unionEq_iff' {t : TileSet ps ιₜ} {s : Set X} :
    UnionEq s t ↔ (⋃ pt ∈ t, (pt : Set X)) = s := by
  rw [unionEq_iff, union_of_mem_eq_iUnion]

@[simp] lemma UnionEq.exists_mem_iff {t : TileSet ps ιₜ} {s : Set X} (h : UnionEq s t) {x : X} :
    (∃ i, x ∈ t i) ↔ x ∈ s := by
  rw [← unionEq_iff'.1 h]
  simp

lemma UnionEq.exists_mem_mem_iff {t : TileSet ps ιₜ} {s : Set X} (h : UnionEq s t) {x : X} :
    (∃ pt ∈ t, x ∈ pt) ↔ x ∈ s := by
  rw [← unionEq_iff'.1 h]
  simp

@[simp] lemma unionEq_reindex_iff_of_surjective {t : TileSet ps ιₜ} {s : Set X} {e : ιₜ' → ιₜ}
    (h : Surjective e) : UnionEq s (t.reindex e) ↔ UnionEq s t :=
  (h.iUnion_comp (fun i ↦ (t i : Set X))).congr_left

@[simp] lemma unionEq_smul_iff {s : Set X} {t : TileSet ps ιₜ} (g : G) :
    UnionEq (g • s) (g • t) ↔ UnionEq s t := by
  simp [unionEq_iff, smul_apply, ← Set.smul_set_iUnion]

lemma unionEq_smul_set_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    UnionEq (g • s) t ↔ UnionEq s (g⁻¹ • t) := by
  nth_rewrite 1 [← one_smul G t]
  rw [← mul_inv_self g, mul_smul, unionEq_smul_iff]

lemma unionEq_smul_tileSet_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    UnionEq s (g • t) ↔ UnionEq (g⁻¹ • s) t := by
  nth_rewrite 2 [← one_smul G t]
  rw [← mul_left_inv g, mul_smul, unionEq_smul_iff]

@[simp] lemma unionEq_empty [IsEmpty ιₜ] (t : TileSet ps ιₜ) : UnionEq ∅ t := by
  simp [unionEq_iff]

/-- Whether the union of the tiles of `t` is the whole of `X`. -/
def UnionEqUniv : TileSetFunction ps Prop ⊤ := (UnionEq Set.univ).ofLE (by simp)

lemma unionEqUniv_iff {t : TileSet ps ιₜ} : UnionEqUniv t ↔ (⋃ i, (t i : Set X)) = Set.univ :=
  Iff.rfl

lemma unionEqUniv_iff' {t : TileSet ps ιₜ} :
    UnionEqUniv t ↔ (⋃ pt ∈ t, (pt : Set X)) = Set.univ := by
  rw [unionEqUniv_iff, union_of_mem_eq_iUnion]

lemma unionEqUniv_iff_unionEq {t : TileSet ps ιₜ} : UnionEqUniv t ↔ UnionEq Set.univ t :=
  Iff.rfl

lemma UnionEqUniv.exists_mem {t : TileSet ps ιₜ} (h : UnionEqUniv t) (x : X) :
    ∃ i, x ∈ t i := by
  rw [unionEqUniv_iff_unionEq] at h
  rw [UnionEq.exists_mem_iff h]
  exact Set.mem_univ _

lemma UnionEqUniv.exists_mem_mem {t : TileSet ps ιₜ} (h : UnionEqUniv t) (x : X) :
    ∃ pt ∈ t, x ∈ pt := by
  rw [unionEqUniv_iff_unionEq] at h
  rw [UnionEq.exists_mem_mem_iff h]
  exact Set.mem_univ _

@[simp] lemma unionEqUniv_reindex_iff_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (h : Surjective e) : UnionEqUniv (t.reindex e) ↔ UnionEqUniv t :=
  unionEq_reindex_iff_of_surjective h

/-- Whether `t` is a tiling of the set `s`. -/
def IsTilingOf (s : Set X) : TileSetFunction ps Prop (MulAction.stabilizer G s) :=
  (TileSet.Disjoint.ofLE (by simp)).comp₂ (UnionEq s) (· ∧ ·)

lemma isTilingOf_iff {t : TileSet ps ιₜ} {s : Set X} : IsTilingOf s t ↔
    (Pairwise fun i j ↦ Disjoint (t i : Set X) (t j)) ∧ (⋃ i, (t i : Set X)) = s :=
  Iff.rfl

lemma isTilingOf_iff' {t : TileSet ps ιₜ} {s : Set X} : IsTilingOf s t ↔
    TileSet.Disjoint t ∧ UnionEq s t :=
  Iff.rfl

lemma IsTilingOf.disjoint {t : TileSet ps ιₜ} {s : Set X} (h : IsTilingOf s t) :
    TileSet.Disjoint t :=
  And.left h

lemma IsTilingOf.unionEq {t : TileSet ps ιₜ} {s : Set X} (h : IsTilingOf s t) :
    UnionEq s t :=
  And.right h

lemma isTilingOf_iff_of_injective {t : TileSet ps ιₜ} {s : Set X} (h : Injective t) :
    IsTilingOf s t ↔ ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ∧
      (⋃ pt ∈ t, (pt : Set X)) = s := by
  rw [isTilingOf_iff, ← TileSet.disjoint_iff, ← coeSet_disjoint_iff_disjoint_of_injective h,
      union_of_mem_eq_iUnion]

@[simp] lemma isTilingOf_smul_iff {s : Set X} {t : TileSet ps ιₜ} (g : G) :
    IsTilingOf (g • s) (g • t) ↔ IsTilingOf s t := by
  apply Iff.and <;> simp

lemma isTilingOf_smul_set_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    IsTilingOf (g • s) t ↔ IsTilingOf s (g⁻¹ • t) := by
  nth_rewrite 1 [← one_smul G t]
  rw [← mul_inv_self g, mul_smul, isTilingOf_smul_iff]

lemma isTilingOf_smul_tileSet_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    IsTilingOf s (g • t) ↔ IsTilingOf (g⁻¹ • s) t := by
  nth_rewrite 2 [← one_smul G t]
  rw [← mul_left_inv g, mul_smul, isTilingOf_smul_iff]

@[simp] lemma isTilingOf_empty [IsEmpty ιₜ] (t : TileSet ps ιₜ) : IsTilingOf ∅ t := by
  simp [isTilingOf_iff, Subsingleton.pairwise]

/-- Whether `t` is a tiling of the whole of `X`. -/
def IsTiling : TileSetFunction ps Prop ⊤ := TileSet.Disjoint.comp₂ (UnionEqUniv) (· ∧ ·)

lemma isTiling_iff {t : TileSet ps ιₜ} : IsTiling t ↔
    (Pairwise fun i j ↦ Disjoint (t i : Set X) (t j)) ∧ (⋃ i, (t i : Set X)) = Set.univ :=
  Iff.rfl

lemma isTiling_iff' {t : TileSet ps ιₜ} : IsTiling t ↔ TileSet.Disjoint t ∧ UnionEqUniv t :=
  Iff.rfl

lemma isTiling_iff_of_injective {t : TileSet ps ιₜ} (h : Injective t) :
    IsTiling t ↔ ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ∧
      (⋃ pt ∈ t, (pt : Set X)) = Set.univ := by
  rw [isTiling_iff, ← TileSet.disjoint_iff, ← coeSet_disjoint_iff_disjoint_of_injective h,
      union_of_mem_eq_iUnion]

lemma IsTiling.disjoint {t : TileSet ps ιₜ} (h : IsTiling t) : TileSet.Disjoint t :=
  And.left h

lemma IsTiling.unionEqUniv {t : TileSet ps ιₜ} (h : IsTiling t) : UnionEqUniv t :=
  And.right h

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

lemma IsTilingOf.finiteIntersections {t : TileSet ps ιₜ} {s : Set X} (h : IsTilingOf s t) :
    FiniteIntersections t :=
  Disjoint.finiteIntersections (IsTilingOf.disjoint h)

lemma IsTiling.finiteIntersections {t : TileSet ps ιₜ} (h : IsTiling t) :
    FiniteIntersections t :=
  Disjoint.finiteIntersections (IsTiling.disjoint h)

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

lemma IsTilingOf.finiteDistinctIntersections {t : TileSet ps ιₜ} {s : Set X}
    (h : TileSet.IsTilingOf s t) : FiniteDistinctIntersections t :=
  FiniteIntersections.finiteDistinctIntersections (IsTilingOf.finiteIntersections h)

lemma IsTiling.finiteDistinctIntersections {t : TileSet ps ιₜ}
    (h : TileSet.IsTiling t) : FiniteDistinctIntersections t :=
  FiniteIntersections.finiteDistinctIntersections (IsTiling.finiteIntersections h)

end TileSet

end Discrete

/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Combinatorics.Tiling.TileSet
import AM.Mathlib.Data.Set.Pairwise.Basic
import AM.Mathlib.Logic.Equiv.Set
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Logic.Equiv.Pairwise

/-!
# Bundled functions on tilings

This file defines bundled functions on tilings in a discrete context.

## Main definitions

* `TileSetFunction ps α s`: A bundled function from `TileSet ps ιₜ` to `α` that is invariant under
change or permutation of index type `ιₜ` and under the action of group elements in `s`.

* `VarTileSetFunction Y ps α s`: A bundled function from `Y` (acted on by `G`) and `TileSet ps ιₜ`
to `α` that is invariant under change or permutation of index type `ιₜ` and under the action of
group elements in `s` on both the value from `Y` and the `TileSet`.

* `TileSet.IsTilingOf s t`: A `VarTileSetFunction` for whether `t` is a tiling of the set `s` of
points.

* `TileSet.IsTiling t`: A `TileSetFunction` for whether `t` is a tiling of `X`.

## References

* Branko Grünbaum and G. C. Shephard, Tilings and Patterns, 1987
-/


noncomputable section

namespace Discrete

open Function
open scoped Pointwise

variable {G X Y ιₚ : Type*} [Group G] [MulAction G X] [MulAction G Y]

universe u
variable {ps : Protoset G X ιₚ} {ιᵤ ιᵤ' : Type u} {ιₜ ιₜ' Eᵤ F α β γ : Type*}
variable [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ] [EquivLike Eᵤ ιᵤ' ιᵤ]

section

variable (Y ps α) (s : Subgroup G)

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

/-- A `VarTileSetFunction Y ps α s` is a function from `Y` and `TileSet ps ιₜ` to `α` that is
invariant under change or permutation of index type `ιₜ` (within the same universe) and under the
action (on both arguments) of group elements in `s`. -/
@[ext] structure VarTileSetFunction where
  /-- The function.  Use the coercion to a function rather than using `toFun` directly. -/
  toFun : {ιₜ : Type u} → Y → TileSet ps ιₜ → α
  /-- The function is invariant under reindexing. -/
  reindex_eq' : ∀ {ιₜ ιₜ' : Type u} (f : ιₜ ≃ ιₜ') (y : Y) (t : TileSet ps ιₜ),
    toFun y (t.reindex f.symm) = toFun y t
  /-- The function is invariant under the group action within the subgroup `s`. -/
  smul_eq : ∀ {ιₜ : Type u} {g : G} (y : Y) (t : TileSet ps ιₜ), g ∈ s →
    toFun (g • y) (g • t) = toFun y t

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
protected def const (a : α) : TileSetFunction ps α s :=
  ⟨fun {ιₜ} ↦ const (TileSet ps ιₜ) a, by simp, by simp⟩

@[simp] lemma const_apply (a : α) (t : TileSet ps ιₜ) : TileSetFunction.const ps s a t = a := rfl

variable {ps s}

instance [Nonempty α] : Nonempty (TileSetFunction ps α s) :=
  ⟨TileSetFunction.const ps s <| Classical.arbitrary _⟩

/-- Composing a `TileSetFunction` with a function on the result type. -/
protected def comp (f : TileSetFunction ps α s) (fab : α → β) : TileSetFunction ps β s :=
  ⟨fab ∘ f.toFun, by simp, fun _ hg ↦ by simp [hg]⟩

@[simp] lemma comp_apply (f : TileSetFunction ps α s) (fab : α → β) (t : TileSet ps ιₜ) :
    f.comp fab t = fab (f t) :=
  rfl

lemma comp_comp (f : TileSetFunction ps α s) (fab : α → β) (fbg : β → γ) :
    f.comp (fbg ∘ fab) = (f.comp fab).comp fbg :=
  rfl

/-- Combining two `TileSetFunction`s with a function on their result types. -/
protected def comp₂ (f : TileSetFunction ps α s) (f' : TileSetFunction ps β s) (fabg : α → β → γ) :
    TileSetFunction ps γ s :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ fabg (f t) (f' t), by simp, fun _ hg ↦ by simp [hg]⟩

@[simp] lemma comp₂_apply (f : TileSetFunction ps α s) (f' : TileSetFunction ps β s)
    (fabg : α → β → γ) (t : TileSet ps ιₜ) : f.comp₂ f' fabg t = fabg (f t) (f' t) :=
  rfl

/-- Converting a `TileSetFunction ps α s` to one using a subgroup of `s`. -/
protected def ofLE (f : TileSetFunction ps α s) {s' : Subgroup G} (h : s' ≤ s) :
    TileSetFunction ps α s' :=
  ⟨f.toFun, by simp, fun _ hg ↦ by simp [SetLike.le_def.1 h hg]⟩

@[simp] lemma ofLE_apply (f : TileSetFunction ps α s) {s' : Subgroup G} (h : s' ≤ s)
    (t : TileSet ps ιₜ) : f.ofLE h t = f t :=
  rfl

variable (ps)

@[simp] lemma ofLE_const (a : α) {s' : Subgroup G} (h : s' ≤ s) :
    (TileSetFunction.const ps s a).ofLE h = TileSetFunction.const ps s' a :=
  rfl

variable {ps}

lemma ofLE_comp (f : TileSetFunction ps α s) (fab : α → β) {s' : Subgroup G} (h : s' ≤ s) :
    (f.comp fab).ofLE h = (f.ofLE h).comp fab :=
  rfl

lemma ofLE_comp₂ (f : TileSetFunction ps α s) (f' : TileSetFunction ps β s) (fabg : α → β → γ)
    {s' : Subgroup G} (h : s' ≤ s) : (f.comp₂ f' fabg).ofLE h = (f.ofLE h).comp₂ (f'.ofLE h) fabg :=
  rfl

end TileSetFunction

namespace VarTileSetFunction

variable (Y ps α) (s : Subgroup G)

instance : CoeFun (VarTileSetFunction Y ps α s) (fun _ ↦ {ιₜ : Type*} → Y → TileSet ps ιₜ → α) where
  coe := toFun

attribute [coe] toFun

attribute [simp] smul_eq

variable {Y ps α s}

@[simp] lemma reindex_eq (f : VarTileSetFunction Y ps α s) (y : Y) (t : TileSet ps ιᵤ) (e : Eᵤ) :
    f y (t.reindex e) = f y t :=
  f.reindex_eq' (EquivLike.toEquiv e).symm y t

@[simp] lemma reindex_eq_of_bijective (f : VarTileSetFunction Y ps α s) (y : Y) (t : TileSet ps ιᵤ)
    {e : ιᵤ' → ιᵤ} (h : Bijective e) : f y (t.reindex e) = f y t :=
  f.reindex_eq y t <| Equiv.ofBijective e h

lemma coe_mk (f : {ιₜ : Type*} → Y → TileSet ps ιₜ → α) (hr hs) :
    (⟨f, hr, hs⟩ : VarTileSetFunction Y ps α s) = @f :=
  rfl

lemma reindex_iff {f : VarTileSetFunction Y ps Prop s} {y : Y} {t : TileSet ps ιᵤ} (e : Eᵤ) :
    f y (t.reindex e) ↔ f y t :=
  by simp

lemma reindex_iff_of_bijective {f : VarTileSetFunction Y ps Prop s} {y : Y} {t : TileSet ps ιᵤ}
    {e : ιᵤ' → ιᵤ} (h : Bijective e) : f y (t.reindex e) ↔ f y t :=
  by simp [h]

lemma smul_iff {f : VarTileSetFunction Y ps Prop s} {g : G} {y : Y} {t : TileSet ps ιₜ}
    (hg : g ∈ s) : f (g • y) (g • t) ↔ f y t :=
  by simp [hg]

lemma eq_of_coeSet_eq_of_injective (f : VarTileSetFunction Y ps α s) (y : Y) {t₁ : TileSet ps ιᵤ}
    {t₂ : TileSet ps ιᵤ'} (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁)
    (h₂ : Injective t₂) : f y t₁ = f y t₂ := by
  rw [← TileSet.reindex_equivOfCoeSetEqOfInjective h h₁ h₂]
  exact (reindex_eq _ _ _ _).symm

lemma iff_of_coeSet_eq_of_injective (f : VarTileSetFunction Y ps Prop s) {y : Y}
    {t₁ : TileSet ps ιᵤ} {t₂ : TileSet ps ιᵤ'} (h : (t₁ : Set (PlacedTile ps)) = t₂)
    (h₁ : Injective t₁) (h₂ : Injective t₂) : f y t₁ ↔ f y t₂ := by
  simpa using f.eq_of_coeSet_eq_of_injective y h h₁ h₂

variable (Y ps s)

/-- The constant `VarTileSetFunction`. -/
protected def const (a : α) : VarTileSetFunction Y ps α s :=
  ⟨fun {ιₜ} ↦ const Y (const (TileSet ps ιₜ) a), by simp, by simp⟩

variable {Y}

@[simp] lemma const_apply (a : α) (y : Y) (t : TileSet ps ιₜ) :
    VarTileSetFunction.const Y ps s a y t = a :=
  rfl

variable {ps s}

instance [Nonempty α] : Nonempty (VarTileSetFunction Y ps α s) :=
  ⟨VarTileSetFunction.const Y ps s <| Classical.arbitrary _⟩

/-- Composing a `VarTileSetFunction` with a function on the result type. -/
protected def comp (f : VarTileSetFunction Y ps α s) (fab : α → β) : VarTileSetFunction Y ps β s :=
  ⟨fun y ↦ fab ∘ (f.toFun y), by simp, fun _ _ hg ↦ by simp [hg]⟩

@[simp] lemma comp_apply (f : VarTileSetFunction Y ps α s) (fab : α → β) (y : Y)
    (t : TileSet ps ιₜ) : f.comp fab y t = fab (f y t) :=
  rfl

lemma comp_comp (f : VarTileSetFunction Y ps α s) (fab : α → β) (fbg : β → γ) :
    f.comp (fbg ∘ fab) = (f.comp fab).comp fbg :=
  rfl

/-- Combining two `VarTileSetFunction`s with a function on their result types. -/
protected def comp₂ (f : VarTileSetFunction Y ps α s) (f' : VarTileSetFunction Y ps β s)
    (fabg : α → β → γ) : VarTileSetFunction Y ps γ s :=
  ⟨fun {ιₜ : Type*} (y : Y) (t : TileSet ps ιₜ) ↦ fabg (f y t) (f' y t),
   by simp,
   fun _ _ hg ↦ by simp [hg]⟩

@[simp] lemma comp₂_apply (f : VarTileSetFunction Y ps α s) (f' : VarTileSetFunction Y ps β s)
    (fabg : α → β → γ) (y : Y) (t : TileSet ps ιₜ) : f.comp₂ f' fabg y t = fabg (f y t) (f' y t) :=
  rfl

/-- Converting a `VarTileSetFunction Y ps α s` to one using a subgroup of `s`. -/
protected def ofLE (f : VarTileSetFunction Y ps α s) {s' : Subgroup G} (h : s' ≤ s) :
    VarTileSetFunction Y ps α s' :=
  ⟨f.toFun, by simp, fun _ _ hg ↦ by simp [SetLike.le_def.1 h hg]⟩

@[simp] lemma ofLE_apply (f : VarTileSetFunction Y ps α s) {s' : Subgroup G} (h : s' ≤ s)
    (y : Y) (t : TileSet ps ιₜ) : f.ofLE h y t = f y t :=
  rfl

variable (Y ps)

@[simp] lemma ofLE_const (a : α) {s' : Subgroup G} (h : s' ≤ s) :
    (VarTileSetFunction.const Y ps s a).ofLE h = VarTileSetFunction.const Y ps s' a :=
  rfl

variable {Y ps}

lemma ofLE_comp (f : VarTileSetFunction Y ps α s) (fab : α → β) {s' : Subgroup G} (h : s' ≤ s) :
    (f.comp fab).ofLE h = (f.ofLE h).comp fab :=
  rfl

lemma ofLE_comp₂ (f : VarTileSetFunction Y ps α s) (f' : VarTileSetFunction Y ps β s)
    (fabg : α → β → γ) {s' : Subgroup G} (h : s' ≤ s) :
    (f.comp₂ f' fabg).ofLE h = (f.ofLE h).comp₂ (f'.ofLE h) fabg :=
  rfl

/-- Converting a `VarTileSetFunction Y ps α s`, acting at `y`, to a
`TileSetFunction ps α (s ⊓ MulAction.stabilizer G y)`. -/
def toTileSetFunction (f : VarTileSetFunction Y ps α s) (y : Y) :
    TileSetFunction ps α (s ⊓ MulAction.stabilizer G y) :=
  ⟨f.toFun y,
   by simp,
   fun {ιₜ} {g} t hg ↦ by
     simp only
     nth_rewrite 1 [← MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hg).2]
     rw [smul_eq _ _ _ (Subgroup.mem_inf.1 hg).1]⟩

@[simp] lemma toTileSetFunction_apply (f : VarTileSetFunction Y ps α s) (y : Y)
    (t : TileSet ps ιₜ) : f.toTileSetFunction y t = f y t :=
  rfl

variable (ps s)

@[simp] lemma toTileSetFunction_const (a : α) (y : Y) :
    (VarTileSetFunction.const Y ps s a).toTileSetFunction y = TileSetFunction.const ps _ a :=
  rfl

variable {ps s}

lemma toTileSetFunction_comp (f : VarTileSetFunction Y ps α s) (fab : α → β) (y : Y) :
    (f.comp fab).toTileSetFunction y = (f.toTileSetFunction y).comp fab :=
  rfl

lemma toTileSetFunction_comp₂ (f : VarTileSetFunction Y ps α s) (f' : VarTileSetFunction Y ps β s)
    (fabg : α → β → γ) (y : Y) : (f.comp₂ f' fabg).toTileSetFunction y =
      (f.toTileSetFunction y).comp₂ (f'.toTileSetFunction y) fabg :=
  rfl

end VarTileSetFunction

namespace TileSetFunction

variable {s : Subgroup G}

variable (Y)

/-- Converting a `TileSetFunction ps α s` to a `VarTileSetFunction Y ps α s` that ignores its
first argument. -/
def toVarTileSetFunction (f : TileSetFunction ps α s) : VarTileSetFunction Y ps α s :=
  ⟨fun {ιₜ} ↦ const Y f.toFun, by simp, fun _ _ hg ↦ by simp [hg]⟩

variable {Y}

@[simp] lemma toVarTileSetFunction_apply (f : TileSetFunction ps α s) (y : Y) (t : TileSet ps ιₜ) :
    f.toVarTileSetFunction Y y t = f t :=
  rfl

variable (Y ps s)

@[simp] lemma toVarTileSetFunction_const (a : α) :
    (TileSetFunction.const ps s a).toVarTileSetFunction Y = VarTileSetFunction.const Y ps s a :=
  rfl

variable {ps s}

lemma toVarTileSetFunction_comp (f : TileSetFunction ps α s) (fab : α → β) :
    (f.comp fab).toVarTileSetFunction Y = (f.toVarTileSetFunction Y).comp fab :=
  rfl

lemma toVarTileSetFunction_comp₂ (f : TileSetFunction ps α s) (f' : TileSetFunction ps β s)
    (fabg : α → β → γ) : (f.comp₂ f' fabg).toVarTileSetFunction Y =
      (f.toVarTileSetFunction Y).comp₂ (f'.toVarTileSetFunction Y) fabg :=
  rfl

lemma toVarTileSetFunction_ofLE  (f : TileSetFunction ps α s) {s' : Subgroup G} (h : s' ≤ s) :
    (f.ofLE h).toVarTileSetFunction Y = (f.toVarTileSetFunction Y).ofLE h :=
  rfl

variable {Y}

@[simp] lemma toVarTileSetFunction_toTileSetFunction (f : TileSetFunction ps α s) (y : Y) :
    (f.toVarTileSetFunction Y).toTileSetFunction y = f.ofLE inf_le_left :=
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

lemma unionEq_smul_set_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    UnionEq (g • s) t ↔ UnionEq s (g⁻¹ • t) := by
  nth_rewrite 1 [← one_smul G t]
  rw [← mul_inv_self g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _

lemma unionEq_smul_tileSet_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    UnionEq s (g • t) ↔ UnionEq (g⁻¹ • s) t := by
  nth_rewrite 2 [← one_smul G t]
  rw [← mul_left_inv g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _

@[simp] lemma unionEq_empty [IsEmpty ιₜ] (t : TileSet ps ιₜ) : UnionEq ∅ t := by
  simp [unionEq_iff]

/-- Whether the union of the tiles of `t` is the whole of `X`. -/
def UnionEqUniv : TileSetFunction ps Prop ⊤ := (UnionEq.toTileSetFunction Set.univ).ofLE (by simp)

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
def IsTilingOf : VarTileSetFunction (Set X) ps Prop ⊤ :=
  (TileSet.Disjoint.toVarTileSetFunction (Set X)).comp₂ UnionEq (· ∧ ·)

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

lemma isTilingOf_smul_set_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    IsTilingOf (g • s) t ↔ IsTilingOf s (g⁻¹ • t) := by
  nth_rewrite 1 [← one_smul G t]
  rw [← mul_inv_self g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _

lemma isTilingOf_smul_tileSet_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    IsTilingOf s (g • t) ↔ IsTilingOf (g⁻¹ • s) t := by
  nth_rewrite 2 [← one_smul G t]
  rw [← mul_left_inv g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _

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

lemma IsTilingOf.finiteDistinctIntersections {t : TileSet ps ιₜ} {s : Set X}
    (h : TileSet.IsTilingOf s t) : FiniteDistinctIntersections t :=
  FiniteIntersections.finiteDistinctIntersections (IsTilingOf.finiteIntersections h)

lemma IsTiling.finiteDistinctIntersections {t : TileSet ps ιₜ}
    (h : TileSet.IsTiling t) : FiniteDistinctIntersections t :=
  FiniteIntersections.finiteDistinctIntersections (IsTiling.finiteIntersections h)

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

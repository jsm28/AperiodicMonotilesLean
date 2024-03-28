/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Combinatorics.Tiling.TileSet

/-!
# Bundled functions on tilings

This file defines bundled functions on tilings in a discrete context.

## Main definitions

* `TileSetFunction ps α s`: A bundled function from `TileSet ps ιₜ` to `α` that is invariant under
change or permutation of index type `ιₜ` and under the action of group elements in `s`.

* `VarTileSetFunction Y ps α s`: A bundled function from `Y` (acted on by `G`) and `TileSet ps ιₜ`
to `α` that is invariant under change or permutation of index type `ιₜ` and under the action of
group elements in `s` on both the value from `Y` and the `TileSet`.

## References

* Branko Grünbaum and G. C. Shephard, Tilings and Patterns, 1987
-/


noncomputable section

namespace Discrete

open Function
open scoped Pointwise

variable {G X Y ιₚ : Type*} [Group G] [MulAction G X] [MulAction G Y]

universe u
variable {ps : Protoset G X ιₚ} {ιᵤ ιᵤ' : Type u} {ιₜ ιₜ' Eᵤ α β γ : Type*}
variable [EquivLike Eᵤ ιᵤ' ιᵤ]

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

end Discrete

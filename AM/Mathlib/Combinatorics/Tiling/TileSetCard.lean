/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Combinatorics.Tiling.TileSet
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cardinality in tilings

This file defines a type for the number of copies of each possible tile in a `TileSet`.

## Main definitions

* `TileSetCard ps`: A number of each image of tiles from the protoset `ps`.

## References

* Branko Grünbaum and G. C. Shephard, Tilings and Patterns, 1987
-/


noncomputable section

namespace Discrete

open Function
open scoped Cardinal Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]

variable {ps : Protoset G X ιₚ} {ιₜ E F : Type*}
universe u
variable {ιᵤ ιᵤ' : Type u} [EquivLike E ιᵤ' ιᵤ] [FunLike F ιᵤ' ιᵤ] [EmbeddingLike F ιᵤ' ιᵤ]

variable (ps)

/-- A `TileSetCard ps` associates a `Cardinal` to each `PlacedTile ps`. This is a separate
definition rather than just using plain functions because of the action by `G`. The main
definition used for tilings is `TileSet`, which uses indexed families; this definition is
intended for use cases where it is convenient for `TileSet`s related by reindexing to be
equal. -/
@[ext] structure TileSetCard where
  /-- The number of each tile. Use the coercion to a function rather than using `tilesCard`
      directly. -/
  tilesCard : PlacedTile ps → Cardinal

variable {ps}

namespace TileSetCard

instance : Inhabited (TileSetCard ps) := ⟨⟨0⟩⟩

instance : CoeFun (TileSetCard ps) (fun _ ↦ PlacedTile ps → Cardinal) where
  coe := tilesCard

attribute [coe] tilesCard

lemma coe_mk (t) : (⟨t⟩ : TileSetCard ps) = t := rfl

@[simp, norm_cast] lemma coe_inj {t₁ t₂ : TileSetCard ps} :
    (t₁ : PlacedTile ps → Cardinal) = t₂ ↔ t₁ = t₂ :=
  TileSetCard.ext_iff.symm

lemma coe_injective :
    Injective (TileSetCard.tilesCard : TileSetCard ps → PlacedTile ps → Cardinal) :=
  fun _ _ ↦ coe_inj.1

instance : PartialOrder (TileSetCard ps) := PartialOrder.lift _ coe_injective

lemma le_def {t₁ t₂ : TileSetCard ps} : t₁ ≤ t₂ ↔ ∀ i, t₁ i ≤ t₂ i :=
  Iff.rfl

instance : MulAction G (TileSetCard ps) where
  smul := fun g t ↦ ⟨fun pt ↦ t (g⁻¹ • pt)⟩
  one_smul := fun t ↦ TileSetCard.ext <| funext <| fun pt ↦ by
    change t _ = _
    simp
  mul_smul := fun g₁ g₂ t ↦ TileSetCard.ext <| funext <| fun pt ↦ by
    change t _ = t _
    convert rfl using 2
    rw [mul_inv_rev, mul_smul]

lemma smul_apply (g : G) (t : TileSetCard ps) (pt : PlacedTile ps) : (g • t) pt = t (g⁻¹ • pt) :=
  rfl

end TileSetCard

namespace TileSet

/-- The number of each tile in the `TileSet`. -/
protected def card (t : TileSet ps ιₜ) : TileSetCard ps :=
  ⟨fun pt ↦ #(t ⁻¹' {pt})⟩

lemma card_apply (t : TileSet ps ιₜ) (pt : PlacedTile ps) : t.card pt = #(t ⁻¹' {pt}) :=
  rfl

lemma card_reindex_le_of_injective (t : TileSet ps ιᵤ) {f : ιᵤ' → ιᵤ} (hf : Injective f) :
    (t.reindex f).card ≤ t.card := by
  simp_rw [TileSetCard.le_def, card_apply, TileSet.coe_reindex, Set.preimage_comp]
  exact fun _ ↦ Cardinal.mk_preimage_of_injective _ _ hf

lemma card_reindex_le_of_embeddingLike (t : TileSet ps ιᵤ) (f : F) : (t.reindex f).card ≤ t.card :=
  t.card_reindex_le_of_injective (EmbeddingLike.injective f)

lemma card_le_card_reindex_of_surjective (t : TileSet ps ιᵤ) {f : ιᵤ' → ιᵤ} (hf : Surjective f) :
    t.card ≤ (t.reindex f).card := by
  simp_rw [TileSetCard.le_def, card_apply, TileSet.coe_reindex, Set.preimage_comp]
  refine fun pt ↦ Cardinal.mk_preimage_of_subset_range _ _ ?_
  simp [Set.range_iff_surjective.2 hf]

lemma card_reindex_of_bijective (t : TileSet ps ιᵤ) {f : ιᵤ' → ιᵤ} (hf : Bijective f) :
    (t.reindex f).card = t.card :=
  le_antisymm (t.card_reindex_le_of_injective hf.injective)
              (t.card_le_card_reindex_of_surjective hf.surjective)

@[simp] lemma card_reindex_of_equivLike (t : TileSet ps ιᵤ) (f : E) : (t.reindex f).card = t.card :=
  t.card_reindex_of_bijective (EquivLike.bijective f)

lemma card_eq_iff_exists_reindex_eq {t₁ : TileSet ps ιᵤ} {t₂ : TileSet ps ιᵤ'} :
    t₁.card = t₂.card ↔ ∃ e : ιᵤ' ≃ ιᵤ, t₁.reindex e = t₂ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simp_rw [TileSetCard.ext_iff, funext_iff, card_apply, Cardinal.eq] at h
    refine ⟨Equiv.ofPreimageEquiv fun pt ↦ (h pt).some.symm, ?_⟩
    simp_rw [TileSet.ext_iff, funext_iff, reindex_apply, Equiv.ofPreimageEquiv_map, implies_true]
  · rintro ⟨e, rfl⟩
    rw [card_reindex_of_equivLike]

lemma card_smul (g : G) (t : TileSet ps ιₜ) : (g • t).card = g • (t.card) := by
  refine TileSetCard.ext <| funext fun pt ↦ ?_
  simp_rw [TileSetCard.smul_apply, card_apply, smul_coe, Set.preimage_comp, Set.preimage_smul,
           Set.smul_set_singleton]

end TileSet

end Discrete

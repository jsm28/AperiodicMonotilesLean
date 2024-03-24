/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Combinatorics.Tiling.Tile
import AM.Mathlib.Logic.Equiv.Pairwise
import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# Tilings

This file defines some basic concepts related to tilings in a discrete context (with definitions
in a continuous context to be developed separately but analogously). For more general discussion
of the approach taken, see `Mathlib.Combinatorics.Tiling.Tile`.

As definitions relating to tilings mostly are meaningful also for collections of tiles that may
overlap or may not cover the whole space, and such collections of tiles are also often of
interest when working with tilings, our formal definitions are generally made for indexed
families of tiles rather than having a specific type limited to a particular notion of tilings,
and further restrictions on such a family are given as hypotheses where needed. Since
collections of possibly overlapping tiles can be of interest, including the case where two tiles
coincide, we work with indexed families rather than sets (as usual, if a set of tiles is more
convenient in a particular case, it may be considered as a family indexed by itself).

## Main definitions

* `TileSet ps ιₜ`: An indexed family of images of tiles from the protoset `ps`.

* `TileSet.symmetryGroup`: The group of symmetries preserving a `TileSet` up to permutation of the
indices.

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
variable {ps : Protoset G X ιₚ} {ιᵤ ιᵤ' : Type u} {ιₜ ιₜ' ιₜ'' E E' Eᵤ F α β γ : Type*}
variable [EquivLike E ιₜ' ιₜ] [EquivLike E' ιₜ'' ιₜ'] [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
variable [EquivLike Eᵤ ιᵤ' ιᵤ]

variable (ps ιₜ)

/-- A `TileSet ps ιₜ` is an indexed family of `PlacedTile ps`. This is a separate definition
rather than just using plain functions to facilitate defining associated API that can be used
with dot notation. -/
@[ext] structure TileSet where
  /-- The tiles in the family. Use the coercion to a function rather than using `tiles`
      directly. -/
  tiles : ιₜ → PlacedTile ps

variable {ps ιₜ}

namespace TileSet

instance [Nonempty ιₚ] : Nonempty (TileSet ps ιₜ) := ⟨⟨fun _ ↦ Classical.arbitrary _⟩⟩

instance [IsEmpty ιₜ] : Unique (TileSet ps ιₜ) where
  default := ⟨isEmptyElim⟩
  uniq := fun _ ↦ TileSet.ext _ _ <| funext isEmptyElim

instance : CoeFun (TileSet ps ιₜ) (fun _ ↦ ιₜ → PlacedTile ps) where
  coe := tiles

attribute [coe] tiles

lemma coe_mk (t) : (⟨t⟩ : TileSet ps ιₜ) = t := rfl

/-- Coercion from a `TileSet` to a set of tiles (losing information about the presence of
duplicate tiles in the `TileSet`). Use the coercion rather than using `coeSet` directly. -/
@[coe] def coeSet : TileSet ps ιₜ → Set (PlacedTile ps) := fun t ↦ Set.range t

instance : CoeOut (TileSet ps ιₜ) (Set (PlacedTile ps)) where
  coe := coeSet

instance : Membership (PlacedTile ps) (TileSet ps ιₜ) where
  mem := fun pt t ↦ pt ∈ (t : Set (PlacedTile ps))

@[simp] lemma mem_coeSet {pt : PlacedTile ps} {t : TileSet ps ιₜ} :
    pt ∈ (t : Set (PlacedTile ps)) ↔ pt ∈ t :=
  Iff.rfl

lemma coeSet_apply (t : TileSet ps ιₜ) : t = Set.range t := rfl

protected lemma mem_def {pt : PlacedTile ps} {t : TileSet ps ιₜ} : pt ∈ t ↔ ∃ i, t i = pt :=
  Iff.rfl

lemma apply_mem (t : TileSet ps ιₜ) (i : ιₜ) : t i ∈ t := Set.mem_range_self i

@[simp] lemma exists_mem_iff {t : TileSet ps ιₜ} {f : PlacedTile ps → Prop} :
    (∃ pt ∈ t, f pt) ↔ ∃ i, f (t i) := by
  simp_rw [← mem_coeSet, coeSet_apply, Set.exists_range_iff]

lemma union_of_mem_eq_iUnion (t : TileSet ps ιₜ) : ⋃ pt ∈ t, (pt : Set X) = ⋃ i, (t i : Set X) := by
  ext x
  simp

lemma nonempty_of_forall_nonempty (t : TileSet ps ιₜ) (h : ∀ i, (ps i : Set X).Nonempty) (i : ιₜ) :
    (t i : Set X).Nonempty :=
  PlacedTile.coe_nonempty_iff.2 (h _)

lemma finite_of_forall_finite (t : TileSet ps ιₜ) (h : ∀ i, (ps i : Set X).Finite) (i : ιₜ) :
    (t i : Set X).Finite :=
  PlacedTile.coe_finite_iff.2 (h _)

/-- Reindex a `TileSet` by composition with a function on index types (typically an equivalence
for it to literally be reindexing, though not required to be one in this definition). -/
def reindex (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) : TileSet ps ιₜ' where
  tiles := ↑t ∘ f

@[simp] lemma coe_reindex (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) : t.reindex f = ↑t ∘ f := rfl

@[simp] lemma reindex_apply (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) (i : ιₜ') :
    t.reindex f i = t (f i) :=
  rfl

@[simp] lemma reindex_id (t : TileSet ps ιₜ) : t.reindex id = t := rfl

@[simp] lemma injective_reindex_iff_injective {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ} (ht : Injective t) :
    Injective (↑t ∘ f) ↔ Injective f :=
  ht.of_comp_iff _

lemma injective_reindex_of_embeddingLike {t : TileSet ps ιₜ} (f : F) (ht : Injective t) :
    Injective (t.reindex f) :=
  (injective_reindex_iff_injective ht).2 <| EmbeddingLike.injective f

@[simp] lemma reindex_reindex (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) (f' : ιₜ'' → ιₜ') :
    (t.reindex f).reindex f' = t.reindex (f ∘ f') :=
  rfl

@[simp] lemma reindex_eq_reindex_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ} {f : ιₜ' → ιₜ}
    (h : Surjective f) : t₁.reindex f = t₂.reindex f ↔ t₁ = t₂ := by
  refine ⟨fun he ↦ TileSet.ext _ _ <| funext <| h.forall.2 fun i ↦ ?_,
          fun he ↦ congrArg₂ _ he rfl⟩
  simp_rw [← reindex_apply, he]

@[simp] lemma reindex_eq_reindex_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ} (f : E) :
    t₁.reindex f = t₂.reindex f ↔ t₁ = t₂ :=
  reindex_eq_reindex_iff_of_surjective (EquivLike.surjective f)

@[simp] lemma reindex_comp_eq_reindex_comp_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ}
    {f₁ f₂ : ιₜ' → ιₜ} {f : ιₜ'' → ιₜ'} (h : Surjective f) :
    t₁.reindex (f₁ ∘ f) = t₂.reindex (f₂ ∘ f) ↔ t₁.reindex f₁ = t₂.reindex f₂ := by
  rw [← reindex_reindex, ← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]

@[simp] lemma reindex_comp_eq_reindex_comp_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ}
    {f₁ f₂ : ιₜ' → ιₜ} (f : E') :
    t₁.reindex (f₁ ∘ f) = t₂.reindex (f₂ ∘ f) ↔ t₁.reindex f₁ = t₂.reindex f₂ :=
  reindex_comp_eq_reindex_comp_iff_of_surjective (EquivLike.surjective f)

@[simp] lemma reindex_comp_eq_reindex_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    {f : ιₜ' → ιₜ} (h : Surjective f) :
    t₁.reindex (f₁ ∘ f) = t₂.reindex f ↔ t₁.reindex f₁ = t₂ := by
  rw [← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]

@[simp] lemma reindex_comp_eq_reindex_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    (f : E) : t₁.reindex (f₁ ∘ f) = t₂.reindex f ↔ t₁.reindex f₁ = t₂ :=
  reindex_comp_eq_reindex_iff_of_surjective (EquivLike.surjective f)

@[simp] lemma reindex_eq_reindex_comp_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    {f : ιₜ' → ιₜ} (h : Surjective f) :
    t₁.reindex f = t₂.reindex (f₁ ∘ f) ↔ t₁ = t₂.reindex f₁ := by
  rw [← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]

@[simp] lemma reindex_eq_reindex_comp_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    (f : E) : t₁.reindex f = t₂.reindex (f₁ ∘ f) ↔ t₁ = t₂.reindex f₁ :=
  reindex_eq_reindex_comp_iff_of_surjective (EquivLike.surjective f)

lemma coeSet_reindex_eq_range_comp (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) :
    (t.reindex f : Set (PlacedTile ps)) = Set.range (t ∘ f) :=
  rfl

lemma coeSet_reindex_subset (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) :
    (t.reindex f : Set (PlacedTile ps)) ⊆ t := Set.range_comp_subset_range f t

lemma mem_of_mem_reindex {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ} {pt : PlacedTile ps}
    (h : pt ∈ t.reindex f) : pt ∈ t :=
  Set.mem_of_mem_of_subset h <| t.coeSet_reindex_subset f

lemma mem_reindex_iff {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ} {pt : PlacedTile ps} :
    pt ∈ (t.reindex f) ↔ ∃ i, t (f i) = pt :=
  Set.mem_range

@[simp] lemma coeSet_reindex_of_surjective (t : TileSet ps ιₜ) {f : ιₜ' → ιₜ} (h : Surjective f) :
    (t.reindex f : Set (PlacedTile ps)) = t :=
  h.range_comp _

@[simp] lemma coeSet_reindex_of_equivLike (t : TileSet ps ιₜ) (f : E) :
    (t.reindex f : Set (PlacedTile ps)) = t :=
  t.coeSet_reindex_of_surjective <| EquivLike.surjective f

@[simp] lemma mem_reindex_iff_of_surjective {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ} {pt : PlacedTile ps}
    (h : Surjective f) : pt ∈ t.reindex f ↔ pt ∈ t :=
  iff_of_eq <| congrArg (pt ∈ ·) <| t.coeSet_reindex_of_surjective h

@[simp] lemma mem_reindex_iff_of_equivLike {t : TileSet ps ιₜ} (f : E) {pt : PlacedTile ps} :
    pt ∈ t.reindex f ↔ pt ∈ t :=
  mem_reindex_iff_of_surjective <| EquivLike.surjective f

/-- If two `TileSet`s have the same set of tiles and no duplicate tiles, this equivalence maps
one index type to the other. -/
def equivOfCoeSetEqOfInjective {t₁ : TileSet ps ιₜ} {t₂ : TileSet ps ιₜ'}
    (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁) (h₂ : Injective t₂) : ιₜ' ≃ ιₜ :=
  ((Equiv.ofInjective t₂ h₂).trans (Equiv.cast (congrArg _ h.symm))).trans
    (Equiv.ofInjective t₁ h₁).symm

@[simp] lemma reindex_equivOfCoeSetEqOfInjective {t₁ : TileSet ps ιₜ} {t₂ : TileSet ps ιₜ'}
    (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁) (h₂ : Injective t₂) :
    t₁.reindex (equivOfCoeSetEqOfInjective h h₁ h₂) = t₂ := by
  ext i : 2
  simp only [equivOfCoeSetEqOfInjective, Equiv.coe_trans, reindex_apply, comp_apply,
             Equiv.ofInjective_apply, Equiv.cast_apply]
  erw [Equiv.apply_ofInjective_symm h₁]
  rw [Subtype.coe_eq_iff]
  simp_rw [coeSet_apply] at h
  refine ⟨h ▸ Set.mem_range_self _, ?_⟩
  rw [cast_eq_iff_heq, Subtype.heq_iff_coe_eq]
  simp [h]

instance : MulAction G (TileSet ps ιₜ) where
  smul := fun g t ↦ ⟨(g • ·) ∘ ↑t⟩
  one_smul := fun _ ↦ TileSet.ext _ _ <| funext <| fun _ ↦ one_smul _ _
  mul_smul := fun _ _ _ ↦ TileSet.ext _ _ <| funext <| fun _ ↦ mul_smul _ _ _

lemma smul_coe (g : G) (t : TileSet ps ιₜ) : (g • t : TileSet ps ιₜ) = (g • ·) ∘ ↑t := rfl

lemma smul_apply (g : G) (t : TileSet ps ιₜ) (i : ιₜ) : (g • t) i = g • (t i) := rfl

@[simp] lemma smul_reindex (g : G) (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) :
    g • (t.reindex f) = (g • t).reindex f :=
  rfl

@[simp] lemma injective_smul_iff (g : G) {t : TileSet ps ιₜ} : Injective (g • t) ↔ Injective t :=
  Injective.of_comp_iff (MulAction.injective g) t

@[simp] lemma coeSet_smul (g : G) (t : TileSet ps ιₜ) :
    (g • t : TileSet ps ιₜ) = g • (t : Set (PlacedTile ps)) := by
  simp [coeSet_apply, smul_coe, Set.range_comp]

@[simp] lemma smul_mem_smul_iff {pt : PlacedTile ps} (g : G) {t : TileSet ps ιₜ} :
    g • pt ∈ g • t ↔ pt ∈ t := by
  rw [← mem_coeSet, ← mem_coeSet, coeSet_smul, Set.smul_mem_smul_set_iff]

lemma mem_smul_iff_smul_inv_mem {pt : PlacedTile ps} {g : G} {t : TileSet ps ιₜ} :
    pt ∈ g • t ↔ g⁻¹ • pt ∈ t := by
  simp_rw [← mem_coeSet, coeSet_smul, Set.mem_smul_set_iff_inv_smul_mem]

lemma mem_inv_smul_iff_smul_mem {pt : PlacedTile ps} {g : G} {t : TileSet ps ιₜ} :
    pt ∈ g⁻¹ • t ↔ g • pt ∈ t := by
  simp_rw [← mem_coeSet, coeSet_smul, Set.mem_inv_smul_set_iff]

@[simp] lemma smul_inter_smul (g : G) (t : TileSet ps ιₜ) (s : Set X) (i : ιₜ) :
    g • s ∩ (g • t) i = g • (s ∩ t i) := by
  simp [smul_apply, Set.smul_set_inter]

/-- The action of both a group element and a permutation of the index type on a `TileSet`, used
in defining the symmetry group. -/
instance : MulAction (G × Equiv.Perm ιₜ) (TileSet ps ιₜ) where
  smul := fun g t ↦ (g.fst • t).reindex g.snd.symm
  one_smul := fun _ ↦ TileSet.ext _ _ <| funext <| fun _ ↦ one_smul _ _
  mul_smul := fun g h t ↦ TileSet.ext _ _ <| funext <| fun i ↦ by
    change (g.1 * h.1) • t ((g.2 * h.2)⁻¹ i) = g.1 • h.1 • t (h.2⁻¹ (g.2⁻¹ i))
    simp [mul_smul]

lemma smul_prod_eq_reindex (g : G) (f : Equiv.Perm ιₜ) (t : TileSet ps ιₜ) :
    (g, f) • t = (g • t).reindex f.symm :=
  rfl

lemma smul_prod_apply (g : G) (f : Equiv.Perm ιₜ) (t : TileSet ps ιₜ) (i : ιₜ) :
    ((g, f) • t) i = g • t (f.symm i) :=
  rfl

@[simp] lemma smul_prod_one (g : G) (t : TileSet ps ιₜ) : (g, (1 : Equiv.Perm ιₜ)) • t = g • t :=
  rfl

@[simp] lemma smul_prod_refl (g : G) (t : TileSet ps ιₜ) :
    (g, (Equiv.refl ιₜ : Equiv.Perm ιₜ)) • t = g • t :=
  rfl

/-- The symmetry group of a `TileSet ps ιₜ` is the subgroup of `G` that preserves the tiles up to
permutation of the indices. -/
def symmetryGroup (t : TileSet ps ιₜ) : Subgroup G :=
  (MulAction.stabilizer (G × Equiv.Perm ιₜ) t).map (MonoidHom.fst _ _)

/-- A group element is in the symmetry group if and only if there is a permutation of the indices
such that mapping by the group element and that permutation preserves the `TileSet`. -/
lemma mem_symmetryGroup_iff_exists {t : TileSet ps ιₜ} {g : G} :
    g ∈ t.symmetryGroup ↔ ∃ f : Equiv.Perm ιₜ, (g • t).reindex f = t := by
  simp_rw [symmetryGroup, Subgroup.mem_map, MulAction.mem_stabilizer_iff]
  change (∃ x : G × Equiv.Perm ιₜ, _ ∧ x.1 = g) ↔ _
  refine ⟨fun ⟨⟨g', f⟩, ⟨h, hg⟩⟩ ↦ ⟨f.symm, ?_⟩, fun ⟨f, h⟩ ↦ ⟨(g, f.symm), h, rfl⟩⟩
  dsimp only at hg
  subst hg
  exact h

/-- If `g` is in the symmetry group, the image of any tile under `g` is in `t`. -/
lemma exists_smul_eq_of_mem_symmetryGroup {t : TileSet ps ιₜ} {g : G} (i : ιₜ)
    (hg : g ∈ t.symmetryGroup) : ∃ j, g • (t i) = t j := by
  rw [mem_symmetryGroup_iff_exists] at hg
  rcases hg with ⟨f, h⟩
  refine ⟨f.symm i, ?_⟩
  nth_rewrite 2 [← h]
  simp [TileSet.smul_apply]

/-- If `g` is in the symmetry group, every tile in `t` is the image under `g` of some tile in
`t`. -/
lemma exists_smul_eq_of_mem_symmetryGroup' {t : TileSet ps ιₜ} {g : G} (i : ιₜ)
    (hg : g ∈ t.symmetryGroup) : ∃ j, g • (t j) = t i := by
  rcases exists_smul_eq_of_mem_symmetryGroup i (inv_mem hg) with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  simp [← hj]

/-- If `g` is in the symmetry group, the image of any tile under `g` is in `t`. -/
lemma smul_mem_of_mem_of_mem_symmetryGroup {t : TileSet ps ιₜ} {g : G} {pt : PlacedTile ps}
    (hg : g ∈ t.symmetryGroup) (hpt : pt ∈ t) : g • pt ∈ t := by
  rcases hpt with ⟨i, rfl⟩
  simp_rw [TileSet.mem_def, eq_comm]
  exact exists_smul_eq_of_mem_symmetryGroup i hg

/-- If `g` is in the symmetry group, every tile in `t` is the image under `g` of some tile in
`t`. -/
lemma exists_smul_eq_of_mem_of_mem_symmetryGroup {t : TileSet ps ιₜ} {g : G} {pt : PlacedTile ps}
    (hg : g ∈ t.symmetryGroup) (hpt : pt ∈ t) : ∃ pt' ∈ t, g • pt' = pt := by
  rcases hpt with ⟨i, rfl⟩
  rw [exists_mem_iff]
  exact exists_smul_eq_of_mem_symmetryGroup' i hg

@[simp] lemma symmetryGroup_of_isEmpty [IsEmpty ιₜ] (t : TileSet ps ιₜ) : t.symmetryGroup = ⊤ := by
  ext g
  rw [mem_symmetryGroup_iff_exists]
  simp only [Subgroup.mem_top, iff_true]
  exact ⟨Equiv.refl _, Subsingleton.elim _ _⟩

@[simp] lemma symmetryGroup_reindex (t : TileSet ps ιₜ) (f : E) :
    (t.reindex f).symmetryGroup = t.symmetryGroup := by
  ext g
  simp_rw [mem_symmetryGroup_iff_exists]
  refine ⟨fun ⟨e, he⟩ ↦ ?_, fun ⟨e, he⟩ ↦ ?_⟩
  · refine ⟨((EquivLike.toEquiv f).symm.trans e).trans (EquivLike.toEquiv f), ?_⟩
    rw [← reindex_eq_reindex_iff_of_equivLike f, ← he]
    simp [comp.assoc]
  · refine ⟨((EquivLike.toEquiv f).trans e).trans (EquivLike.toEquiv f).symm, ?_⟩
    nth_rewrite 2 [← he]
    simp [← comp.assoc]

@[simp] lemma symmetryGroup_reindex_of_bijective (t : TileSet ps ιₜ) {f : ιₜ' → ιₜ}
    (h : Bijective f) : (t.reindex f).symmetryGroup = t.symmetryGroup :=
  t.symmetryGroup_reindex <| Equiv.ofBijective f h

/-- Mapping the `TileSet` by a group element acts on the symmetry group by conjugation. -/
lemma symmetryGroup_smul (t : TileSet ps ιₜ) (g : G) :
    (g • t).symmetryGroup = (ConjAct.toConjAct g) • t.symmetryGroup := by
  simp_rw [← smul_prod_one, symmetryGroup, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  ext h
  simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, MulEquiv.coe_toMonoidHom,
             MulAut.conj_apply, Prod.inv_mk, inv_one, Prod.exists, Prod.mk_mul_mk, one_mul,
             mul_one, MonoidHom.coe_fst, Prod.mk.injEq, exists_eq_right_right, exists_and_right,
             exists_eq_right, Subgroup.mem_smul_pointwise_iff_exists, ConjAct.smul_def,
             ConjAct.ofConjAct_toConjAct]
  rw [exists_comm]
  convert Iff.rfl
  rw [exists_and_right]

lemma mem_symmetryGroup_smul_iff {t : TileSet ps ιₜ} (g : G) {g' : G} :
    g * g' * g⁻¹ ∈ (g • t).symmetryGroup ↔ g' ∈ t.symmetryGroup := by
  simp [symmetryGroup_smul, Subgroup.mem_smul_pointwise_iff_exists, ConjAct.smul_def]

lemma mem_symmetryGroup_smul_iff' {t : TileSet ps ιₜ} {g g' : G} :
    g' ∈ (g • t).symmetryGroup ↔ g⁻¹ * g' * g ∈ t.symmetryGroup := by
  convert mem_symmetryGroup_smul_iff g
  simp [mul_assoc]

lemma symmetryGroup_le_stabilizer_coeSet (t : TileSet ps ιₜ) :
    t.symmetryGroup ≤ MulAction.stabilizer G (t : Set (PlacedTile ps)) := by
  simp_rw [SetLike.le_def, mem_symmetryGroup_iff_exists, MulAction.mem_stabilizer_iff]
  rintro g ⟨f, hf⟩
  nth_rewrite 2 [← hf]
  simp

lemma symmetryGroup_eq_stabilizer_coeSet_of_injective (t : TileSet ps ιₜ) (h : Injective t) :
    t.symmetryGroup = MulAction.stabilizer G (t : Set (PlacedTile ps)) := by
  refine le_antisymm t.symmetryGroup_le_stabilizer_coeSet ?_
  simp_rw [SetLike.le_def, mem_symmetryGroup_iff_exists, MulAction.mem_stabilizer_iff]
  intro g hg
  rw [← coeSet_smul] at hg
  exact ⟨equivOfCoeSetEqOfInjective hg ((injective_smul_iff g).2 h) h, by simp⟩

end TileSet

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

end TileSet

end Discrete

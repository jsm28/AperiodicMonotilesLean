/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Logic.Equiv.Pairwise
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.GroupTheory.Coset

/-!
# Tilings

This file defines some basic concepts related to tilings in a discrete context (with definitions
in a continuous context to be developed separately but analogously).

Work in the field of tilings does not generally try to define or state things in any kind of
maximal generality, so it is necessary to adapt definitions and statements from the literature
to produce something that seems appropriately general for mathlib, covering a wide range of
tiling-related concepts found in the literature. Nevertheless, further generalization may prove
of use as this work is extended in future.

We work in the context of a space `X` acted on by a group `G`; the action is not required to be
faithful, although typically it is. In a discrete context, tiles are expected to cover the space,
or a subset of it being tiled when working with tilings not of the whole space, and the tiles are
pairwise disjoint. In a continuous context, definitions in the literature vary; the tiles may be
closed and cover the space with interiors may be required to be disjoint (as used by Grünbaum and
Shephard or Goodman-Strauss), or they may be required to be measurable and to partition it up to
null sets (as used by Greenfeld and Tao).

In general we are concerned not with a tiling in isolation but with tilings by some protoset of
tiles; thus we make definitions in the context of such a protoset, where copies of the tiles in
the tiling must be images of those tiles under the action of an element of the given group.

As definitions relating to tilings mostly are meaningful also for collections of tiles that may
overlap or may not cover the whole space, and such collections of tiles are also often of
interest when working with tilings, our formal definitions are generally made for indexed
families of tiles rather than having a specific type limited to a particular notion of tilings,
and further restrictions on such a family are given as hypotheses where needed. Since
collections of possibly overlapping tiles can be of interest, including the case where two tiles
coincide, we work with indexed families rather than sets (as usual, if a set of tiles is more
convenient in a particular case, it may be considered as a family indexed by itself).

Where there are matching rules that say what combinations of tiles are considered as valid, these
are provided as separate hypotheses where required. Tiles in a protoset are commonly considered
in the literature to be marked in some way. When this is simply to distinguish two otherwise
identical tiles, this is represented by the use of different indices in the protoset. When this
is to give a file fewer symmetries than it would otherwise have under the action of the given
group, this is represented by the symmetries specified in the `Prototile` being less than its
full stabilizer.

The group `G` is throughout here a multiplicative group. Additive groups are also used in the
literature, typically when based on `ℤ`; when working with the definitions here, such cases are
expected to be handled by working with a group such as `Fin n → Multiplicative ℤ`.

## Main definitions

* `Prototile G X`: A prototile in `X` as acted on by `G`, carrying the information of a subgroup
  of the stabilizer that says when two copies of the prototile are considered the same.

* `Protoset G X ιₚ`: An indexed family of prototiles.

* `PlacedTile ps`: An image of a tile in the protoset `ps`.

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
* Chaim Goodman-Strauss, [Open Questions in
  Tiling](https://strauss.hosted.uark.edu/papers/survey.pdf)
* Rachel Greenfeld and Terence Tao, [A counterexample to the periodic tiling
  conjecture](https://arxiv.org/abs/2211.15847)
-/


noncomputable section

namespace Discrete

open Function
open scoped Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]

variable (G X)

/-- A `Prototile G X` describes a tile in `X`, copies of which under elements of `G` may be used
in tilings. Two copies related by an element of `symmetries` are considered the same; two copies
not so related, even if they have the same points, are considered distinct. -/
@[ext] structure Prototile where
  /-- The points in the prototile. Use the coercion to `Set X`, or `∈` on the `Prototile`, rather
      than using `carrier` directly. -/
  carrier : Set X
  /-- The group elements considered symmetries of the prototile. -/
  symmetries : Subgroup (MulAction.stabilizer G carrier)

variable {G X}

namespace Prototile

instance : Inhabited (Prototile G X) where
  default := ⟨∅, ⊥⟩

instance : CoeOut (Prototile G X) (Set X) where
  coe := Prototile.carrier

attribute [coe] carrier

instance : Membership X (Prototile G X) where
  mem := fun x p ↦ x ∈ (p : Set X)

lemma coe_mk (c s) : (⟨c, s⟩ : Prototile G X) = c := rfl

@[simp] lemma mem_coe {x : X} {p : Prototile G X} : x ∈ (p : Set X) ↔ x ∈ p := Iff.rfl

end Prototile

variable (G X ιₚ)

/-- A `Protoset G X ιₚ` is an indexed family of `Prototile G X`. This is a separate definition
rather than just using plain functions to facilitate defining associated API that can be used
with dot notation. -/
@[ext] structure Protoset where
  /-- The tiles in the protoset. Use the coercion to a function rather than using `tiles`
      directly. -/
  tiles : ιₚ → Prototile G X

variable {G X ιₚ}

namespace Protoset

instance : Inhabited (Protoset G X ιₚ) where
  default := ⟨fun _ ↦ default⟩

instance : CoeFun (Protoset G X ιₚ) (fun _ ↦ ιₚ → Prototile G X) where
  coe := tiles

attribute [coe] tiles

lemma coe_mk (t) : (⟨t⟩ : Protoset G X ιₚ) = t := rfl

end Protoset

universe u
variable (ps : Protoset G X ιₚ) {ιᵤ ιᵤ' : Type u} {ιₜ ιₜ' ιₜ'' E E' Eᵤ F α β γ : Type*}
variable [EquivLike E ιₜ' ιₜ] [EquivLike E' ιₜ'' ιₜ'] [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
variable [EquivLike Eᵤ ιᵤ' ιᵤ]

/-- A `PlacedTile ps` is an image of a tile in the protoset `p` under an element of the group `G`.
This is represented using a quotient so that images under group elements differing only by a
symmetry of the tile are equal. -/
@[ext] structure PlacedTile where
  /-- The index of the tile in the protoset. -/
  index : ιₚ
  /-- The group elements under which this tile is an image. -/
  groupElts : G ⧸ ((ps index).symmetries.map <| Subgroup.subtype _)

variable {ps}

namespace PlacedTile

instance [Nonempty ιₚ] : Nonempty (PlacedTile ps) := ⟨⟨Classical.arbitrary _, (1 : G)⟩⟩

/-- An induction principle to deduce results for `PlacedTile` from those given an index and an
element of `G`, used with `induction pt using PlacedTile.induction_on`. -/
@[elab_as_elim] protected lemma induction_on {ppt : PlacedTile ps → Prop} (pt : PlacedTile ps)
    (h : ∀ i : ιₚ, ∀ gx : G, ppt ⟨i, gx⟩) : ppt pt := by
  rcases pt with ⟨i, gx⟩
  exact Quotient.inductionOn' gx (h i)

/-- An alternative extensionality principle for `PlacedTile` that avoids `HEq`, using existence
of a common group element. -/
lemma ext_iff_of_exists {pt₁ pt₂ : PlacedTile ps} :
    pt₁ = pt₂ ↔ pt₁.index = pt₂.index ∧ ∃ g, ⟦g⟧ = pt₁.groupElts ∧ ⟦g⟧ = pt₂.groupElts := by
  refine ⟨fun h ↦ ?_, fun ⟨h, g, hg₁, hg₂⟩ ↦ ?_⟩
  · subst h
    simp only [and_self, true_and]
    refine ⟨pt₁.groupElts.out', ?_⟩
    rw [← @Quotient.mk''_eq_mk, Quotient.out_eq']
  · rcases pt₁ with ⟨i₁, g₁⟩
    rcases pt₂ with ⟨i₂, g₂⟩
    dsimp only at h
    subst h
    ext
    · rfl
    · exact heq_of_eq (hg₁.symm.trans hg₂)

/-- An alternative extensionality principle for `PlacedTile` that avoids `HEq`, using equality
of quotient preimages. -/
lemma ext_iff_of_preimage {pt₁ pt₂ : PlacedTile ps} :
    pt₁ = pt₂ ↔ pt₁.index = pt₂.index ∧
      (Quotient.mk _) ⁻¹' {pt₁.groupElts} = (Quotient.mk _) ⁻¹' {pt₂.groupElts} := by
  refine ⟨fun h ↦ ?_, fun ⟨hi, hq⟩ ↦ ?_⟩
  · subst h
    simp only [and_self, true_and]
  · rcases pt₁ with ⟨i₁, g₁⟩
    rcases pt₂ with ⟨i₂, g₂⟩
    dsimp only at hi
    subst hi
    ext
    · rfl
    · exact heq_of_eq (Set.singleton_eq_singleton_iff.1
        ((Set.preimage_eq_preimage Quotient.surjective_Quotient_mk'').1 hq))

/-- Coercion from a `PlacedTile` to a set of points. Use the coercion rather than using `coeSet`
directly. -/
@[coe] def coeSet : PlacedTile ps → Set X :=
  fun pt ↦ Quotient.liftOn' pt.groupElts (fun g ↦ g • (ps pt.index : Set X))
    fun a b r ↦ by
      rw [QuotientGroup.leftRel_eq] at r
      simp only
      rw [eq_comm, ← inv_smul_eq_iff, smul_smul, ← MulAction.mem_stabilizer_iff]
      exact SetLike.le_def.1 (Subgroup.map_subtype_le _) r

instance : CoeOut (PlacedTile ps) (Set X) where
  coe := coeSet

instance : Membership X (PlacedTile ps) where
  mem := fun x p ↦ x ∈ (p : Set X)

@[simp] lemma mem_coe {x : X} {pt : PlacedTile ps} : x ∈ (pt : Set X) ↔ x ∈ pt := Iff.rfl

lemma coe_mk_mk (i : ιₚ) (g : G) : (⟨i, ⟦g⟧⟩ : PlacedTile ps) = g • (ps i : Set X) := rfl

lemma coe_mk_coe (i : ιₚ) (g : G) : (⟨i, g⟩ : PlacedTile ps) = g • (ps i : Set X) := rfl

lemma coe_nonempty_iff {pt : PlacedTile ps} :
    (pt : Set X).Nonempty ↔ (ps pt.index : Set X).Nonempty := by
  rcases pt with ⟨index, groupElts⟩
  simp only [coeSet]
  rw [← groupElts.out_eq', Quotient.liftOn'_mk'']
  simp

@[simp] lemma coe_mk_nonempty_iff {i : ιₚ} (g) :
    ((⟨i, g⟩ : PlacedTile ps) : Set X).Nonempty ↔ (ps i : Set X).Nonempty :=
  coe_nonempty_iff

lemma coe_finite_iff {pt : PlacedTile ps} :
    (pt : Set X).Finite ↔ (ps pt.index : Set X).Finite := by
  rcases pt with ⟨index, groupElts⟩
  simp only [coeSet]
  rw [← groupElts.out_eq', Quotient.liftOn'_mk'']
  simp

@[simp] lemma coe_mk_finite_iff {i : ιₚ} (g) :
    ((⟨i, g⟩ : PlacedTile ps) : Set X).Finite ↔ (ps i : Set X).Finite :=
  coe_finite_iff

instance : MulAction G (PlacedTile ps) where
  smul := fun g pt ↦ Quotient.liftOn' pt.groupElts (fun h ↦ ⟨pt.index, g * h⟩)
    fun a b r ↦ by
      rw [QuotientGroup.leftRel_eq] at r
      refine PlacedTile.ext _ _ rfl ?_
      simpa [QuotientGroup.eq, ← mul_assoc] using r
  one_smul := fun pt ↦ by
    simp only [HSMul.hSMul]
    induction pt using PlacedTile.induction_on
    simp
  mul_smul := fun x y pt ↦ by
    simp only [HSMul.hSMul]
    induction pt using PlacedTile.induction_on
    simp [mul_assoc]

@[simp] lemma smul_mk_mk (g h : G) (i : ιₚ) : g • (⟨i, ⟦h⟧⟩ : PlacedTile ps) = ⟨i, g * h⟩ := rfl

@[simp] lemma smul_mk_coe (g h : G) (i : ιₚ) : g • (⟨i, h⟩ : PlacedTile ps) = ⟨i, g * h⟩ := rfl

@[simp] lemma smul_index (g : G) (pt : PlacedTile ps) : (g • pt).index = pt.index := by
  induction pt using PlacedTile.induction_on
  rfl

@[simp] lemma coe_smul (g : G) (pt : PlacedTile ps) :
    (g • pt : PlacedTile ps) = g • (pt : Set X) := by
  induction pt using PlacedTile.induction_on
  simp [coeSet, mul_smul]

end PlacedTile

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

lemma unionEq_iff {t : TileSet ps ιₜ} {s : Set X} :
    TileSet.UnionEq s t ↔ (⋃ i, (t i : Set X)) = s :=
  Iff.rfl

lemma unionEq_iff' {t : TileSet ps ιₜ} {s : Set X} :
    TileSet.UnionEq s t ↔ (⋃ pt ∈ t, (pt : Set X)) = s := by
  rw [unionEq_iff, union_of_mem_eq_iUnion]

@[simp] lemma unionEq_reindex_iff_of_surjective {t : TileSet ps ιₜ} {s : Set X} {e : ιₜ' → ιₜ}
    (h : Surjective e) : TileSet.UnionEq s (t.reindex e) ↔ TileSet.UnionEq s t :=
  (h.iUnion_comp (fun i ↦ (t i : Set X))).congr_left

@[simp] lemma unionEq_smul_iff {s : Set X} {t : TileSet ps ιₜ} (g : G) :
    TileSet.UnionEq (g • s) (g • t) ↔ TileSet.UnionEq s t := by
  simp [unionEq_iff, TileSet.smul_apply, ← Set.smul_set_iUnion]

lemma unionEq_smul_set_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    TileSet.UnionEq (g • s) t ↔ TileSet.UnionEq s (g⁻¹ • t) := by
  nth_rewrite 1 [← one_smul G t]
  rw [← mul_inv_self g, mul_smul, unionEq_smul_iff]

lemma unionEq_smul_tileSet_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    TileSet.UnionEq s (g • t) ↔ TileSet.UnionEq (g⁻¹ • s) t := by
  nth_rewrite 2 [← one_smul G t]
  rw [← mul_left_inv g, mul_smul, unionEq_smul_iff]

@[simp] lemma unionEq_empty [IsEmpty ιₜ] (t : TileSet ps ιₜ) : TileSet.UnionEq ∅ t := by
  simp [unionEq_iff]

/-- Whether the union of the tiles of `t` is the whole of `X`. -/
def UnionEqUniv : TileSetFunction ps Prop ⊤ := (UnionEq Set.univ).ofLE (by simp)

lemma unionEqUniv_iff {t : TileSet ps ιₜ} :
    TileSet.UnionEqUniv t ↔ (⋃ i, (t i : Set X)) = Set.univ :=
  Iff.rfl

lemma unionEqUniv_iff' {t : TileSet ps ιₜ} :
    TileSet.UnionEqUniv t ↔ (⋃ pt ∈ t, (pt : Set X)) = Set.univ := by
  rw [unionEqUniv_iff, union_of_mem_eq_iUnion]

@[simp] lemma unionEqUniv_reindex_iff_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (h : Surjective e) : TileSet.UnionEqUniv (t.reindex e) ↔ TileSet.UnionEqUniv t :=
  unionEq_reindex_iff_of_surjective h

/-- Whether `t` is a tiling of the set `s`. -/
def IsTilingOf (s : Set X) : TileSetFunction ps Prop (MulAction.stabilizer G s) :=
  (TileSet.Disjoint.ofLE (by simp)).comp₂ (UnionEq s) (· ∧ ·)

lemma isTilingOf_iff {t : TileSet ps ιₜ} {s : Set X} : IsTilingOf s t ↔
    (Pairwise fun i j ↦ Disjoint (t i : Set X) (t j)) ∧ (⋃ i, (t i : Set X)) = s :=
  Iff.rfl

lemma isTilingOf_iff_of_injective {t : TileSet ps ιₜ} {s : Set X} (h : Injective t) :
    IsTilingOf s t ↔ ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ∧
      (⋃ pt ∈ t, (pt : Set X)) = s := by
  rw [isTilingOf_iff, ← TileSet.disjoint_iff, ← coeSet_disjoint_iff_disjoint_of_injective h,
      union_of_mem_eq_iUnion]

@[simp] lemma isTilingOf_smul_iff {s : Set X} {t : TileSet ps ιₜ} (g : G) :
    TileSet.IsTilingOf (g • s) (g • t) ↔ TileSet.IsTilingOf s t := by
  apply Iff.and <;> simp

lemma isTilingOf_smul_set_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    TileSet.IsTilingOf (g • s) t ↔ TileSet.IsTilingOf s (g⁻¹ • t) := by
  nth_rewrite 1 [← one_smul G t]
  rw [← mul_inv_self g, mul_smul, isTilingOf_smul_iff]

lemma isTilingOf_smul_tileSet_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    TileSet.IsTilingOf s (g • t) ↔ TileSet.IsTilingOf (g⁻¹ • s) t := by
  nth_rewrite 2 [← one_smul G t]
  rw [← mul_left_inv g, mul_smul, isTilingOf_smul_iff]

@[simp] lemma isTilingOf_empty [IsEmpty ιₜ] (t : TileSet ps ιₜ) :
    TileSet.IsTilingOf ∅ t := by
  simp [isTilingOf_iff, Subsingleton.pairwise]

/-- Whether `t` is a tiling of the whole of `X`. -/
def IsTiling : TileSetFunction ps Prop ⊤ := TileSet.Disjoint.comp₂ (UnionEqUniv) (· ∧ ·)

lemma isTiling_iff {t : TileSet ps ιₜ} : IsTiling t ↔
    (Pairwise fun i j ↦ Disjoint (t i : Set X) (t j)) ∧ (⋃ i, (t i : Set X)) = Set.univ :=
  Iff.rfl

lemma isTiling_iff_of_injective {t : TileSet ps ιₜ} (h : Injective t) :
    IsTiling t ↔ ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ∧
      (⋃ pt ∈ t, (pt : Set X)) = Set.univ := by
  rw [isTiling_iff, ← TileSet.disjoint_iff, ← coeSet_disjoint_iff_disjoint_of_injective h,
      union_of_mem_eq_iUnion]

end TileSet

end Discrete

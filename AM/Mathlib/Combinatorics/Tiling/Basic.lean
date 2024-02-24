/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import AM.Mathlib.Logic.Equiv.Defs
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

* `PlacedTile p`: An image of a tile in the protoset `p`.

* `TileSet p ιₜ`: An indexed family of images of tiles from the protoset `p`.

* `TileSet.symmetryGroup`: The group of symmetries preserving a `TileSet` up to permutation of the
indices.

* `TileSetFunction p Y s`: A bundled function from `TileSet p ιₜ` to `Y` that is invariant under
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

variable (G : Type*) (X : Type*) (ιₚ : Type*) [Group G] [MulAction G X]

/-- A `Prototile G X` describes a tile in `X`, copies of which under elements of `G` may be used
in tilings. Two copies related by an element of `symmetries` are considered the same; two copies
not so related, even if they have the same points, are considered distinct. -/
@[ext] structure Prototile where
  /-- The points in the prototile. Use the coercion to `Set X`, or `∈` on the `Prototile`, rather
      than using `carrier` directly. -/
  carrier : Set X
  /-- The group elements considered symmetries of the prototile. -/
  symmetries : Subgroup (MulAction.stabilizer G carrier)

namespace Prototile

instance : Inhabited (Prototile G X) where
  default := ⟨∅, ⊥⟩

instance : CoeTC (Prototile G X) (Set X) where
  coe := Prototile.carrier

attribute [coe] carrier

instance : Membership X (Prototile G X) where
  mem := fun x p ↦ x ∈ (p : Set X)

variable {G X}

lemma coe_mk (c s) : (⟨c, s⟩ : Prototile G X) = c := rfl

@[simp] lemma mem_coe {x : X} {p : Prototile G X} : x ∈ (p : Set X) ↔ x ∈ p := Iff.rfl

end Prototile

/-- A `Protoset G X ιₚ` is an indexed family of `Prototile G X`. This is a separate definition
rather than just using plain functions to facilitate defining associated API that can be used
with dot notation. -/
@[ext] structure Protoset where
  /-- The tiles in the protoset. Use the coercion to a function rather than using `tiles`
      directly. -/
  tiles : ιₚ → Prototile G X

namespace Protoset

instance : Inhabited (Protoset G X ιₚ) where
  default := ⟨fun _ ↦ default⟩

instance : CoeFun (Protoset G X ιₚ) (fun _ ↦ ιₚ → Prototile G X) where
  coe := tiles

attribute [coe] tiles

variable {G X ιₚ}

lemma coe_mk (t) : (⟨t⟩ : Protoset G X ιₚ) = t := rfl

end Protoset

variable {G X ιₚ}

/-- A `PlacedTile p` is an image of a tile in the protoset `p` under an element of the group `G`.
This is represented using a quotient so that images under group elements differing only by a
symmetry of the tile are equal. -/
@[ext] structure PlacedTile (p : Protoset G X ιₚ) where
  /-- The index of the tile in the protoset. -/
  index : ιₚ
  /-- The group elements under which this tile is an image. -/
  groupElts : G ⧸ ((p index).symmetries.map <| Subgroup.subtype _)

namespace PlacedTile

variable {p : Protoset G X ιₚ}

instance [Nonempty ιₚ] : Nonempty (PlacedTile p) := ⟨⟨Classical.arbitrary _, (1 : G)⟩⟩

/-- An induction principle to deduce results for `PlacedTile` from those given an index and an
element of `G`, used with `induction pt using PlacedTile.induction_on`. -/
@[elab_as_elim] protected lemma induction_on {ppt : PlacedTile p → Prop} (pt : PlacedTile p)
    (h : ∀ i : ιₚ, ∀ gx : G, ppt ⟨i, gx⟩) : ppt pt := by
  rcases pt with ⟨i, gx⟩
  exact Quotient.inductionOn' gx (h i)

/-- Coercion from a `PlacedTile` to a set of points. Use the coercion rather than using `coeSet`
directly. -/
@[coe] def coeSet : PlacedTile p → Set X :=
  fun pt ↦ Quotient.liftOn' pt.groupElts (fun g ↦ g • (p pt.index : Set X))
    fun a b r ↦ by
      rw [QuotientGroup.leftRel_eq] at r
      simp only
      rw [eq_comm, ← inv_smul_eq_iff, smul_smul, ← MulAction.mem_stabilizer_iff]
      exact SetLike.le_def.1 (Subgroup.map_subtype_le _) r

instance : CoeTC (PlacedTile p) (Set X) where
  coe := coeSet

instance : Membership X (PlacedTile p) where
  mem := fun x p ↦ x ∈ (p : Set X)

@[simp] lemma mem_coe {x : X} {pt : PlacedTile p} : x ∈ (pt : Set X) ↔ x ∈ pt := Iff.rfl

lemma coe_mk_mk (i : ιₚ) (g : G) : (⟨i, ⟦g⟧⟩ : PlacedTile p) = g • (p i : Set X) := rfl

lemma coe_mk_coe (i : ιₚ) (g : G) : (⟨i, g⟩ : PlacedTile p) = g • (p i : Set X) := rfl

instance : MulAction G (PlacedTile p) where
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

@[simp] lemma smul_mk_mk (g h : G) (i : ιₚ) : g • (⟨i, ⟦h⟧⟩ : PlacedTile p) = ⟨i, g * h⟩ := rfl

@[simp] lemma smul_mk_coe (g h : G) (i : ιₚ) : g • (⟨i, h⟩ : PlacedTile p) = ⟨i, g * h⟩ := rfl

@[simp] lemma smul_index (g : G) (pt : PlacedTile p) : (g • pt).index = pt.index := by
  induction pt using PlacedTile.induction_on
  rfl

@[simp] lemma coe_smul (g : G) (pt : PlacedTile p) :
    (g • pt : PlacedTile p) = g • (pt : Set X) := by
  induction pt using PlacedTile.induction_on
  simp [coeSet, mul_smul]

end PlacedTile

/-- A `TileSet p ιₜ` is an indexed family of `PlacedTile p`. This is a separate definition
rather than just using plain functions to facilitate defining associated API that can be used
with dot notation. -/
@[ext] structure TileSet (p : Protoset G X ιₚ) (ιₜ : Type*) where
  /-- The tiles in the family. Use the coercion to a function rather than using `tiles`
      directly. -/
  tiles : ιₜ → PlacedTile p

namespace TileSet

variable {p : Protoset G X ιₚ} {ιₜ : Type*}

instance [Nonempty ιₚ] : Nonempty (TileSet p ιₜ) := ⟨⟨fun _ ↦ Classical.arbitrary _⟩⟩

instance : CoeFun (TileSet p ιₜ) (fun _ ↦ ιₜ → PlacedTile p) where
  coe := tiles

attribute [coe] tiles

lemma coe_mk (t) : (⟨t⟩ : TileSet p ιₜ) = t := rfl

/-- Reindex a `TileSet` by composition with a function on index types (typically an equivalence
for it to literally be reindexing, though not required to be one in this definition). -/
def reindex {ιₜ' : Type*} (t : TileSet p ιₜ) (f : ιₜ' → ιₜ) : TileSet p ιₜ' where
  tiles := ↑t ∘ f

@[simp] lemma coe_reindex {ιₜ' : Type*} (t : TileSet p ιₜ) (f : ιₜ' → ιₜ) : t.reindex f = ↑t ∘ f :=
  rfl

@[simp] lemma reindex_apply {ιₜ' : Type*} (t : TileSet p ιₜ) (f : ιₜ' → ιₜ) (i : ιₜ') :
    t.reindex f i = t (f i) := rfl

@[simp] lemma reindex_id (t : TileSet p ιₜ) : t.reindex id = t := rfl

@[simp] lemma reindex_reindex {ιₜ' : Type*} {ιₜ'' : Type*} (t : TileSet p ιₜ) (f : ιₜ' → ιₜ)
    (f' : ιₜ'' → ιₜ') : (t.reindex f).reindex f' = t.reindex (f ∘ f') :=
  rfl

@[simp] lemma reindex_eq_reindex_iff_of_surjective {ιₜ' : Type*} {t₁ t₂ : TileSet p ιₜ}
    {f : ιₜ' → ιₜ} (h : Surjective f) : t₁.reindex f = t₂.reindex f ↔ t₁ = t₂ := by
  refine ⟨fun he ↦ TileSet.ext _ _ <| funext <| h.forall.2 fun i ↦ ?_,
          fun he ↦ congrArg₂ _ he rfl⟩
  simp_rw [← reindex_apply, he]

@[simp] lemma reindex_eq_reindex_iff_of_equivLike {ιₜ' : Type*} {F : Type*} [EquivLike F ιₜ' ιₜ]
    {t₁ t₂ : TileSet p ιₜ} (f : F) : t₁.reindex f = t₂.reindex f ↔ t₁ = t₂ :=
  reindex_eq_reindex_iff_of_surjective (EquivLike.surjective f)

@[simp] lemma reindex_comp_eq_reindex_comp_iff_of_surjective {ιₜ' : Type*} {ιₜ'' : Type*}
    {t₁ t₂ : TileSet p ιₜ} {f₁ f₂ : ιₜ' → ιₜ} {f : ιₜ'' → ιₜ'} (h : Surjective f) :
    t₁.reindex (f₁ ∘ f) = t₂.reindex (f₂ ∘ f) ↔ t₁.reindex f₁ = t₂.reindex f₂ := by
  rw [← reindex_reindex, ← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]

@[simp] lemma reindex_comp_eq_reindex_comp_iff_of_equivLike {ιₜ' : Type*} {ιₜ'' : Type*}
    {F : Type*} [EquivLike F ιₜ'' ιₜ'] {t₁ t₂ : TileSet p ιₜ} {f₁ f₂ : ιₜ' → ιₜ} (f : F) :
    t₁.reindex (f₁ ∘ f) = t₂.reindex (f₂ ∘ f) ↔ t₁.reindex f₁ = t₂.reindex f₂ :=
  reindex_comp_eq_reindex_comp_iff_of_surjective (EquivLike.surjective f)

@[simp] lemma reindex_comp_eq_reindex_iff_of_surjective {ιₜ' : Type*}
    {t₁ t₂ : TileSet p ιₜ} {f₁ : ιₜ → ιₜ} {f : ιₜ' → ιₜ} (h : Surjective f) :
    t₁.reindex (f₁ ∘ f) = t₂.reindex f ↔ t₁.reindex f₁ = t₂ := by
  rw [← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]

@[simp] lemma reindex_comp_eq_reindex_iff_of_equivLike {ιₜ' : Type*} {F : Type*}
    [EquivLike F ιₜ' ιₜ] {t₁ t₂ : TileSet p ιₜ} {f₁ : ιₜ → ιₜ} (f : F) :
    t₁.reindex (f₁ ∘ f) = t₂.reindex f ↔ t₁.reindex f₁ = t₂ :=
  reindex_comp_eq_reindex_iff_of_surjective (EquivLike.surjective f)

@[simp] lemma reindex_eq_reindex_comp_iff_of_surjective {ιₜ' : Type*}
    {t₁ t₂ : TileSet p ιₜ} {f₁ : ιₜ → ιₜ} {f : ιₜ' → ιₜ} (h : Surjective f) :
    t₁.reindex f = t₂.reindex (f₁ ∘ f) ↔ t₁ = t₂.reindex f₁ := by
  rw [← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]

@[simp] lemma reindex_eq_reindex_comp_iff_of_equivLike {ιₜ' : Type*} {F : Type*}
    [EquivLike F ιₜ' ιₜ] {t₁ t₂ : TileSet p ιₜ} {f₁ : ιₜ → ιₜ} (f : F) :
    t₁.reindex f = t₂.reindex (f₁ ∘ f) ↔ t₁ = t₂.reindex f₁ :=
  reindex_eq_reindex_comp_iff_of_surjective (EquivLike.surjective f)

instance : MulAction G (TileSet p ιₜ) where
  smul := fun g t ↦ ⟨(g • ·) ∘ ↑t.tiles⟩
  one_smul := fun _ ↦ TileSet.ext _ _ <| funext <| fun _ ↦ one_smul _ _
  mul_smul := fun _ _ _ ↦ TileSet.ext _ _ <| funext <| fun _ ↦ mul_smul _ _ _

lemma smul_apply (g : G) (t : TileSet p ιₜ) (i : ιₜ) : (g • t) i = g • (t i) := rfl

@[simp] lemma smul_reindex {ιₜ' : Type*} (g : G) (t : TileSet p ιₜ) (f : ιₜ' → ιₜ) :
    g • (t.reindex f) = (g • t).reindex f :=
  rfl

/-- The action of both a group element and a permutation of the index type on a `TileSet`, used
in defining the symmetry group. -/
instance : MulAction (G × Equiv.Perm ιₜ) (TileSet p ιₜ) where
  smul := fun g t ↦ (g.fst • t).reindex g.snd.symm
  one_smul := fun _ ↦ TileSet.ext _ _ <| funext <| fun _ ↦ one_smul _ _
  mul_smul := fun g h t ↦ TileSet.ext _ _ <| funext <| fun i ↦ by
    change (g.1 * h.1) • t ((g.2 * h.2)⁻¹ i) = g.1 • h.1 • t (h.2⁻¹ (g.2⁻¹ i))
    simp [mul_smul]

lemma smul_prod_eq_reindex (g : G) (f : Equiv.Perm ιₜ) (t : TileSet p ιₜ) :
    (g, f) • t = (g • t).reindex f.symm :=
  rfl

lemma smul_prod_apply (g : G) (f : Equiv.Perm ιₜ) (t : TileSet p ιₜ) (i : ιₜ) :
    ((g, f) • t) i = g • t (f.symm i) :=
  rfl

/-- The symmetry group of a `TileSet p ιₜ` is the subgroup of `G` that preserves the tiles up to
permutation of the indices. -/
def symmetryGroup (t : TileSet p ιₜ) : Subgroup G :=
  (MulAction.stabilizer (G × Equiv.Perm ιₜ) t).map (MonoidHom.fst _ _)

/-- A group element is in the symmetry group if and only if there is a permutation of the indices
such that mapping by the group element and that permutation preserves the `TileSet`. -/
lemma mem_symmetryGroup_iff_exists {t : TileSet p ιₜ} {g : G} :
    g ∈ t.symmetryGroup ↔ ∃ f : Equiv.Perm ιₜ, (g • t).reindex f = t := by
  simp_rw [symmetryGroup, Subgroup.mem_map, MulAction.mem_stabilizer_iff]
  change (∃ x : G × Equiv.Perm ιₜ, _ ∧ x.1 = g) ↔ _
  refine ⟨fun ⟨⟨g', f⟩, ⟨h, hg⟩⟩ ↦ ⟨f.symm, ?_⟩, fun ⟨f, h⟩ ↦ ⟨(g, f.symm), h, rfl⟩⟩
  dsimp only at hg
  subst hg
  exact h

/-- If `g` is in the symmetry group, the image of any tile under `g` is in `t`. -/
lemma exists_smul_eq_of_mem_symmetryGroup {t : TileSet p ιₜ} {g : G} (i : ιₜ)
    (hg : g ∈ t.symmetryGroup) : ∃ j, g • (t i) = t j := by
  rw [mem_symmetryGroup_iff_exists] at hg
  rcases hg with ⟨f, h⟩
  refine ⟨f.symm i, ?_⟩
  nth_rewrite 2 [← h]
  simp [TileSet.smul_apply]

/-- If `g` is in the symmetry group, every tile in `t` is the image under `g` of some tile in
`t`. -/
lemma exists_smul_eq_of_mem_symmetryGroup' {t : TileSet p ιₜ} {g : G} (i : ιₜ)
    (hg : g ∈ t.symmetryGroup) : ∃ j, g • (t j) = t i := by
  rcases exists_smul_eq_of_mem_symmetryGroup i (inv_mem hg) with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  simp [← hj]

@[simp] lemma symmetryGroup_reindex {ιₜ' : Type*} {F : Type*} [EquivLike F ιₜ' ιₜ]
    (t : TileSet p ιₜ) (f : F) : (t.reindex f).symmetryGroup = t.symmetryGroup := by
  ext g
  simp_rw [mem_symmetryGroup_iff_exists]
  refine ⟨fun ⟨e, he⟩ ↦ ?_, fun ⟨e, he⟩ ↦ ?_⟩
  · refine ⟨((EquivLike.toEquiv f).symm.trans e).trans (EquivLike.toEquiv f), ?_⟩
    rw [← reindex_eq_reindex_iff_of_equivLike f, ← he]
    simp [comp.assoc]
  · refine ⟨((EquivLike.toEquiv f).trans e).trans (EquivLike.toEquiv f).symm, ?_⟩
    nth_rewrite 2 [← he]
    simp [← comp.assoc]

/-- Mapping the `TileSet` by a group element acts on the symmetry group by conjugation. -/
lemma symmetryGroup_smul (t : TileSet p ιₜ) (g : G) : (g • t).symmetryGroup = (ConjAct.toConjAct g) • t.symmetryGroup := by
  ext h
  simp_rw [Subgroup.mem_smul_pointwise_iff_exists, mem_symmetryGroup_iff_exists]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun ⟨f, ⟨e, he⟩, hh⟩ ↦ ⟨e, ?_⟩⟩
  · refine ⟨(ConjAct.toConjAct g)⁻¹ • h, ?_⟩
    simp only [smul_inv_smul, and_true]
    refine ⟨f, ?_⟩
    simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    rw [← smul_left_cancel_iff g, ← hf]
    simp [←mul_smul, ←mul_assoc]
  · subst hh
    nth_rewrite 2 [← he]
    simp [ConjAct.smul_def, mul_smul]

end TileSet

universe u

/-- A `TileSetFunction p Y s` is a function from `TileSet p ιₜ` to `Y` that is invariant under
change or permutation of index type `ιₜ` (within the same universe) and under the action of group
elements in `s`. -/
@[ext] structure TileSetFunction (p : Protoset G X ιₚ) (Y : Type*) (s : Subgroup G) where
  /-- The function.  Use the coercion to a function rather than using `toFun` directly. -/
  toFun : {ιₜ : Type u} → TileSet p ιₜ → Y
  /-- The function is invariant under reindexing. -/
  reindex_eq' : ∀ {ιₜ ιₜ' : Type u} (f : ιₜ ≃ ιₜ') (t : TileSet p ιₜ),
    toFun (t.reindex f.symm) = toFun t
  /-- The function is invariant under the group action within the subgroup `s`. -/
  smul_eq : ∀ {ιₜ : Type u} {g : G} (t : TileSet p ιₜ), g ∈ s → toFun (g • t) = toFun t

namespace TileSetFunction

variable (p : Protoset G X ιₚ) (Y : Type*) (s : Subgroup G)

instance : CoeFun (TileSetFunction p Y s) (fun _ ↦ {ιₜ : Type*} → TileSet p ιₜ → Y) where
  coe := toFun

attribute [coe] toFun

attribute [simp] smul_eq

variable {p Y s}

@[simp] lemma reindex_eq {ιₜ ιₜ' : Type u} {F : Type*} [EquivLike F ιₜ' ιₜ]
    (f : TileSetFunction p Y s) (t : TileSet p ιₜ) (e : F) : f (t.reindex e) = f t :=
  f.reindex_eq' (EquivLike.toEquiv e).symm t

@[simp] lemma reindex_eq_of_bijective {ιₜ ιₜ' : Type u} (f : TileSetFunction p Y s)
    (t : TileSet p ιₜ) {e : ιₜ' → ιₜ} (h : Bijective e) : f (t.reindex e) = f t :=
  f.reindex_eq t <| Equiv.ofBijective e h

lemma coe_mk (f : {ιₜ : Type*} → TileSet p ιₜ → Y) (hr hs) :
    (⟨f, hr, hs⟩ : TileSetFunction p Y s) = @f :=
  rfl

variable (p s)

/-- The constant `TileSetFunction`. -/
protected def const (y : Y) : TileSetFunction p Y s :=
  ⟨fun {ιₜ} ↦ const (TileSet p ιₜ) y, by simp, by simp⟩

@[simp] lemma const_apply (y : Y) {ιₜ : Type*} (t : TileSet p ιₜ) :
  TileSetFunction.const p s y t = y := rfl

variable {p s}

instance [Nonempty Y] : Nonempty (TileSetFunction p Y s) :=
  ⟨TileSetFunction.const p s <| Classical.arbitrary _⟩

/-- Composing a `TileSetFunction` with a function on the result type. -/
protected def comp {Z : Type*} (f : TileSetFunction p Y s) (fyz : Y → Z) : TileSetFunction p Z s :=
  ⟨fyz ∘ f.toFun, by simp, fun _ hg ↦ by simp [hg]⟩

@[simp] lemma comp_apply {Z : Type*} (f : TileSetFunction p Y s) (fyz : Y → Z) {ιₜ : Type*}
    (t : TileSet p ιₜ) : f.comp fyz t = fyz (f t) :=
  rfl

/-- Combining two `TileSetFunction`s with a function on their result types. -/
protected def comp₂ {Y' : Type*} {Z : Type*} (f : TileSetFunction p Y s)
    (f' : TileSetFunction p Y' s) (fyz : Y → Y' → Z) : TileSetFunction p Z s :=
  ⟨fun {ιₜ : Type*} (t : TileSet p ιₜ) ↦ fyz (f t) (f' t), by simp, fun _ hg ↦ by simp [hg]⟩

@[simp] lemma comp₂_apply {Y' : Type*} {Z : Type*} (f : TileSetFunction p Y s)
    (f' : TileSetFunction p Y' s) (fyz : Y → Y' → Z) {ιₜ : Type*} (t : TileSet p ιₜ) :
    f.comp₂ f' fyz t = fyz (f t) (f' t) :=
  rfl

/-- Converting a `TileSetFunction p Y s` to one using a subgroup of `s`. -/
protected def ofLE (f : TileSetFunction p Y s) {s' : Subgroup G} (h : s' ≤ s) :
    TileSetFunction p Y s' :=
  ⟨f.toFun, by simp, fun _ hg ↦ by simp [SetLike.le_def.1 h hg]⟩

@[simp] lemma ofLE_apply (f : TileSetFunction p Y s) {s' : Subgroup G} (h : s' ≤ s) {ιₜ : Type*}
    (t : TileSet p ιₜ) : f.ofLE h t = f t :=
  rfl

end TileSetFunction

namespace TileSet

variable {p : Protoset G X ιₚ}

/-- Whether the tiles of `t` are pairwise disjoint. -/
protected def Disjoint : TileSetFunction p Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet p ιₜ) ↦ Pairwise fun i j ↦ Disjoint (t i : Set X) (t j),
   by
     intro ιₜ ιₜ' f t
     simp only [eq_iff_iff]
     convert EquivLike.pairwise_comp_iff f.symm _
     rfl,
   by simp [TileSet.smul_apply]⟩

protected lemma disjoint_iff {ιₜ : Type*} {t : TileSet p ιₜ} :
    TileSet.Disjoint t ↔ Pairwise fun i j ↦ Disjoint (t i : Set X) (t j) :=
  Iff.rfl

/-- Whether the union of the tiles of `t` is the set `s`. -/
def UnionEq (s : Set X) : TileSetFunction p Prop (MulAction.stabilizer G s) :=
  ⟨fun {ιₜ : Type*} (t : TileSet p ιₜ) ↦ (⋃ i, (t i : Set X)) = s,
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

lemma unionEq_iff {ιₜ : Type*} {t : TileSet p ιₜ} {s : Set X} :
    TileSet.UnionEq s t ↔ (⋃ i, (t i : Set X)) = s :=
  Iff.rfl

/-- Whether the union of the tiles of `t` is the whole of `X`. -/
def UnionEqUniv : TileSetFunction p Prop ⊤ := (UnionEq Set.univ).ofLE (by simp)

lemma unionEqUniv_iff {ιₜ : Type*} {t : TileSet p ιₜ} :
    TileSet.UnionEqUniv t ↔ (⋃ i, (t i : Set X)) = Set.univ :=
  Iff.rfl

/-- Whether `t` is a tiling of the set `s`. -/
def IsTilingOf (s : Set X) : TileSetFunction p Prop (MulAction.stabilizer G s) :=
  (TileSet.Disjoint.ofLE (by simp)).comp₂ (UnionEq s) (· ∧ ·)

lemma isTilingOf_iff {ιₜ : Type*} {t : TileSet p ιₜ} {s : Set X} :
    IsTilingOf s t ↔
    (Pairwise fun i j ↦ Disjoint (t i : Set X) (t j)) ∧ (⋃ i, (t i : Set X)) = s :=
  Iff.rfl

/-- Whether `t` is a tiling of the whole of `X`. -/
def IsTiling : TileSetFunction p Prop ⊤ := TileSet.Disjoint.comp₂ (UnionEqUniv) (· ∧ ·)

lemma isTiling_iff {ιₜ : Type*} {t : TileSet p ιₜ} :
    IsTiling t ↔
    (Pairwise fun i j ↦ Disjoint (t i : Set X) (t j)) ∧ (⋃ i, (t i : Set X)) = Set.univ :=
  Iff.rfl

end TileSet

end Discrete

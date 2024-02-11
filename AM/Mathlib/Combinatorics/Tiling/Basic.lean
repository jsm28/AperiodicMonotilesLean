/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
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

## References

* Branko Grünbaum and G. C. Shephard, Tilings and Patterns, 1987
* Chaim Goodman-Strauss, [Open Questions in
  Tiling](https://strauss.hosted.uark.edu/papers/survey.pdf)
* Rachel Greenfeld and Terence Tao, [A counterexample to the periodic tiling
  conjecture](https://arxiv.org/abs/2211.15847)
-/


noncomputable section

namespace Discrete

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
      rw [eq_comm, ←inv_smul_eq_iff, smul_smul, ←MulAction.mem_stabilizer_iff]
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
      simpa [QuotientGroup.eq, ←mul_assoc] using r
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

end Discrete

import Mathlib.GroupTheory.GroupAction.Basic

open Function

attribute [to_additive] MulAction.pretransitive_iff_subsingleton_quotient
attribute [to_additive] MulAction.pretransitive_iff_unique_quotient_of_nonempty

namespace MulAction
variable {M G α : Type*} [Group G] [Monoid M] [MulAction G α] [MulAction M α]

@[to_additive]
lemma orbit_submonoid_subset (S : Submonoid M) (a : α) : orbit S a ⊆ orbit M a := by
  rintro b ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]
lemma mem_orbit_of_mem_orbit_submonoid {S : Submonoid M} {a b : α} (h : a ∈ orbit S b) :
    a ∈ orbit M b :=
  orbit_submonoid_subset S _ h

@[to_additive]
lemma orbit_subgroup_subset (H : Subgroup G) (a : α) : orbit H a ⊆ orbit G a :=
  orbit_submonoid_subset H.toSubmonoid a

@[to_additive]
lemma mem_orbit_of_mem_orbit_subgroup {H : Subgroup G} {a b : α} (h : a ∈ orbit H b) :
    a ∈ orbit G b :=
  orbit_subgroup_subset H _ h

@[to_additive]
lemma orbitRel_subgroup_le (H : Subgroup G) : orbitRel H α ≤ orbitRel G α :=
  Setoid.le_def.2 mem_orbit_of_mem_orbit_subgroup

@[to_additive]
lemma mem_orbit_symm {a₁ a₂ : α} : a₁ ∈ orbit G a₂ ↔ a₂ ∈ orbit G a₁ := by
  simp_rw [← orbit_eq_iff, eq_comm]

@[to_additive]
lemma orbitRel.Quotient.orbit_injective :
    Injective (orbitRel.Quotient.orbit : orbitRel.Quotient G α → Set α) := by
  intro x y h
  simp_rw [orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq', orbit_eq_iff] at h
  change @Setoid.r _ (orbitRel G _) _ _ at h
  simpa [← Quotient.eq''] using h

@[to_additive (attr := simp)]
lemma orbitRel.Quotient.orbit_inj {x y : orbitRel.Quotient G α} : x.orbit = y.orbit ↔ x = y :=
  orbitRel.Quotient.orbit_injective.eq_iff

@[to_additive]
lemma orbitRel.quotient_eq_of_quotient_subgroup_eq {H : Subgroup G} {a b : α}
    (h : (⟦a⟧ : orbitRel.Quotient H α) = ⟦b⟧) : (⟦a⟧ : orbitRel.Quotient G α) = ⟦b⟧ := by
  rw [@Quotient.eq] at h ⊢
  exact mem_orbit_of_mem_orbit_subgroup h

@[to_additive]
lemma orbitRel.quotient_eq_of_quotient_subgroup_eq' {H : Subgroup G} {a b : α}
    (h : (Quotient.mk'' a : orbitRel.Quotient H α) = Quotient.mk'' b) :
    (Quotient.mk'' a : orbitRel.Quotient G α) = Quotient.mk'' b :=
  orbitRel.quotient_eq_of_quotient_subgroup_eq h

@[to_additive]
nonrec lemma orbitRel.Quotient.orbit_nonempty (x : orbitRel.Quotient G α) :
    Set.Nonempty x.orbit := by
  rw [orbitRel.Quotient.orbit_eq_orbit_out x Quotient.out_eq']
  exact orbit_nonempty _

@[to_additive]
nonrec lemma orbitRel.Quotient.mapsTo_smul_orbit (g : G) (x : orbitRel.Quotient G α) :
    Set.MapsTo (g • ·) x.orbit x.orbit := by
  rw [orbitRel.Quotient.orbit_eq_orbit_out x Quotient.out_eq']
  exact mapsTo_smul_orbit g x.out'

@[to_additive]
instance (x : orbitRel.Quotient G α) : MulAction G x.orbit where
  smul g := (orbitRel.Quotient.mapsTo_smul_orbit g x).restrict _ _ _
  one_smul a := Subtype.ext (one_smul G (a : α))
  mul_smul g g' a' := Subtype.ext (mul_smul g g' (a' : α))

@[to_additive (attr := simp)]
lemma orbitRel.Quotient.orbit.coe_smul {g : G} {x : orbitRel.Quotient G α} {a : x.orbit} :
    ↑(g • a) = g • (a : α) :=
  rfl

@[to_additive]
instance (x : orbitRel.Quotient G α) : IsPretransitive G x.orbit where
  exists_smul_eq := by
    induction x using Quotient.inductionOn'
    rintro ⟨y, yh⟩ ⟨z, zh⟩
    rw [orbitRel.Quotient.mem_orbit, Quotient.eq''] at yh zh
    rcases yh with ⟨g, rfl⟩
    rcases zh with ⟨h, rfl⟩
    refine ⟨h * g⁻¹, ?_⟩
    ext
    simp [mul_smul]

-- TODO version for plain MulAction.orbit as well.
@[to_additive]
lemma orbitRel.Quotient.mem_subgroup_orbit_iff {H : Subgroup G} {x : orbitRel.Quotient G α}
    {a b : x.orbit} : a ∈ MulAction.orbit H b ↔ (a : α) ∈ MulAction.orbit H (b : α) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with ⟨g, rfl⟩
    simp_rw [Submonoid.smul_def, Subgroup.coe_toSubmonoid, orbit.coe_smul, ← Submonoid.smul_def]
    exact MulAction.mem_orbit _ g
  · rcases h with ⟨g, h⟩
    simp_rw [Submonoid.smul_def, Subgroup.coe_toSubmonoid, ← orbit.coe_smul,
             ← Submonoid.smul_def, ← Subtype.ext_iff] at h
    subst h
    exact MulAction.mem_orbit _ g

@[to_additive]
lemma orbitRel.Quotient.subgroup_quotient_eq_iff {H : Subgroup G} {x : orbitRel.Quotient G α}
    {a b : x.orbit} : (⟦a⟧ : orbitRel.Quotient H x.orbit) = ⟦b⟧ ↔
      (⟦↑a⟧ : orbitRel.Quotient H α) = ⟦↑b⟧ := by
  simp_rw [← @Quotient.mk''_eq_mk, Quotient.eq'']
  exact orbitRel.Quotient.mem_subgroup_orbit_iff

@[to_additive]
lemma orbitRel.Quotient.mem_subgroup_orbit_iff' {H : Subgroup G} {x : orbitRel.Quotient G α}
    {a b : x.orbit} {c : α} (h : (⟦a⟧ : orbitRel.Quotient H x.orbit) = ⟦b⟧) :
    (a : α) ∈ MulAction.orbit H c ↔ (b : α) ∈ MulAction.orbit H c := by
  simp_rw [mem_orbit_symm (a₂ := c)]
  convert Iff.rfl using 2
  rw [orbit_eq_iff]
  suffices hb : ↑b ∈ orbitRel.Quotient.orbit (⟦a⟧ : orbitRel.Quotient H x.orbit) by
    rw [orbitRel.Quotient.orbit_eq_orbit_out (⟦a⟧ : orbitRel.Quotient H x.orbit) Quotient.out_eq']
       at hb
    rw [← orbitRel.Quotient.mem_subgroup_orbit_iff]
    convert hb using 1
    rw [orbit_eq_iff]
    change @Setoid.r _ (orbitRel H _) _ _
    rw [← Quotient.eq'', Quotient.out_eq', @Quotient.mk''_eq_mk]
  rw [orbitRel.Quotient.mem_orbit, h, @Quotient.mk''_eq_mk]

end MulAction

import Mathlib.GroupTheory.GroupAction.Basic

open Function

namespace MulAction
variable {M G α : Type*} [Group G] [Monoid M] [MulAction G α] [MulAction M α]

@[to_additive]
lemma fst_mem_orbit_of_mem_orbit {β : Type*} [MulAction M β] {x y : α × β}
    (h : x ∈ MulAction.orbit M y) : x.1 ∈ MulAction.orbit M y.1 := by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]
lemma snd_mem_orbit_of_mem_orbit {β : Type*} [MulAction M β] {x y : α × β}
    (h : x ∈ MulAction.orbit M y) : x.2 ∈ MulAction.orbit M y.2 := by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

variable (G α)

@[to_additive]
lemma orbitRel_le_fst (β : Type*) [MulAction G β] :
    orbitRel G (α × β) ≤ (orbitRel G α).comap Prod.fst :=
  Setoid.le_def.2 fst_mem_orbit_of_mem_orbit

@[to_additive]
lemma orbitRel_le_snd (β : Type*) [MulAction G β] :
    orbitRel G (α × β) ≤ (orbitRel G β).comap Prod.snd :=
  Setoid.le_def.2 snd_mem_orbit_of_mem_orbit

variable {G α}

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

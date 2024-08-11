import Mathlib.GroupTheory.Index

namespace Subgroup

open Cardinal

variable {G G' : Type*} [Group G] [Group G'] {H K : Subgroup G}

@[to_additive]
lemma exists_pow_mem_of_index_ne_zero (h : H.index ≠ 0) (a : G) : ∃ n, 0 < n ∧ n ≤ H.index ∧ a ^ n ∈ H := by
  suffices ∃ n₁ n₂, n₁ < n₂ ∧ n₂ ≤ H.index ∧ ((a ^ n₂ : G) : G ⧸ H) = ((a ^ n₁ : G) : G ⧸ H) by
    rcases this with ⟨n₁, n₂, hlt, hle, he⟩
    refine ⟨n₂ - n₁, by omega, by omega, ?_⟩
    rw [eq_comm, QuotientGroup.eq, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add,
        add_comm] at he
    rw [← zpow_natCast]
    convert he
    omega
  suffices ∃ n₁ n₂, n₁ ≠ n₂ ∧ n₁ ≤ H.index ∧ n₂ ≤ H.index ∧
      ((a ^ n₂ : G) : G ⧸ H) = ((a ^ n₁ : G) : G ⧸ H) by
    rcases this with ⟨n₁, n₂, hne, hle₁, hle₂, he⟩
    rcases hne.lt_or_lt with hlt | hlt
    · exact ⟨n₁, n₂, hlt, hle₂, he⟩
    · exact ⟨n₂, n₁, hlt, hle₁, he.symm⟩
  by_contra hc
  simp_rw [not_exists] at hc
  let f : (Set.Icc 0 H.index) → G ⧸ H := fun n ↦ (a ^ (n : ℕ) : G)
  have hf : Function.Injective f := by
    rintro ⟨n₁, h₁, hle₁⟩ ⟨n₂, h₂, hle₂⟩ he
    have hc' := hc n₁ n₂
    dsimp only [f] at he
    simpa [hle₁, hle₂, he] using hc'
  have := (fintypeOfIndexNeZero h).finite
  have hcard := Finite.card_le_of_injective f hf
  simp [← index_eq_card] at hcard

@[to_additive]
lemma exists_pow_mem_of_relindex_ne_zero (h : H.relindex K ≠ 0) {a : G} (ha : a ∈ K) :
    ∃ n, 0 < n ∧ n ≤ H.relindex K ∧ a ^ n ∈ H ⊓ K := by
  rcases exists_pow_mem_of_index_ne_zero h ⟨a, ha⟩ with ⟨n, hlt, hle, he⟩
  refine ⟨n, hlt, hle, ?_⟩
  simpa [pow_mem ha, mem_subgroupOf] using he

@[to_additive]
lemma pow_mem_of_index_ne_zero_of_dvd (h : H.index ≠ 0) (a : G) {n : ℕ}
    (hn : ∀ m, 0 < m → m ≤ H.index → m ∣ n) : a ^ n ∈ H := by
  rcases exists_pow_mem_of_index_ne_zero h a with ⟨m, hlt, hle, he⟩
  rcases hn m hlt hle with ⟨k, rfl⟩
  rw [pow_mul]
  exact pow_mem he _

@[to_additive]
lemma pow_mem_of_relindex_ne_zero_of_dvd (h : H.relindex K ≠ 0) {a : G} (ha : a ∈ K) {n : ℕ}
    (hn : ∀ m, 0 < m → m ≤ H.relindex K → m ∣ n) : a ^ n ∈ H ⊓ K := by
  convert pow_mem_of_index_ne_zero_of_dvd h ⟨a, ha⟩ hn
  simp [pow_mem ha, mem_subgroupOf]

end Subgroup

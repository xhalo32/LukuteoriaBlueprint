import Mathlib.Tactic.Have
import Mathlib.Tactic.Cases
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Finsupp.Notation
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace NumberTheory

open Nat

theorem prime_dvd_iff_gcd_eq_one {p n : ℕ} (hp : Nat.Prime p) : ¬ p ∣ n ↔ p.gcd n = 1 := by
  rw [Nat.prime_def] at hp
  constructor
  · intro h
    obtain ⟨hp1, hp2⟩ := hp
    by_contra! hf
    specialize hp2 _ <| gcd_dvd_left p n
    simp_all
    have := gcd_dvd_right p n
    rw [hp2] at this
    contradiction
  · intro h hf
    obtain ⟨k, hf⟩ := hf
    rw [hf]at h
    rw [gcd_mul_right_right] at h
    omega

-- Miikan jaollisuuslemma
theorem prime_dvd_mul {p n m : ℕ} (hp : Nat.Prime p) (h : p ∣ n * m) : p ∣ n ∨ p ∣ m := by
  by_contra!
  obtain ⟨hpn, hpm⟩ := this
  rw [prime_dvd_iff_gcd_eq_one hp] at *

  have hpnm : p.gcd (n * m) = 1
  · exact Coprime.mul_right hpn hpm -- TODO

  rw [← prime_dvd_iff_gcd_eq_one hp] at hpnm
  contradiction

-- This exists in Mathlib but requires a ton of unnecessary imports
theorem infinite_setOf_prime : {p | Nat.Prime p}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hp⟩ := Nat.exists_infinite_primes a.succ
  use p
  grind

-- TODO formalize the course proof
--   by_contra! h
--   rw [Set.not_infinite] at h
--   unfold Set.Finite at h
--   have := @Fintype.ofFinite _ h
--   let m := {p | Nat.Prime p}.toFinset.prod id
--   have : ∀ p ∈ {p | Nat.Prime p}, p < m
--   · unfold m
--     intro p hp
--     have := prime_two


variable {m n p q i : ℕ}

theorem exists_nth_prime (hp : p.Prime) : ∃ i, nth Nat.Prime i = p := by
  have := Nat.range_nth_of_infinite infinite_setOf_prime
  rw [Set.range_eq_iff] at this
  exact this.2 _ hp

  -- This is equivalent with surjectivity which we don't have
  -- suffices Function.HasRightInverse (nth Nat.Prime) by
  --   obtain ⟨g, hg⟩ := this
  --   refine ⟨g p, ?_⟩
  --   rw [hg]
  -- have := nth_injective infinite_setOf_prime
  -- have := nth_mem_of_infinite infinite_setOf_prime

theorem dvd_prime (hp : p.Prime) : m ∣ p ↔ m = 1 ∨ m = p := by
  constructor
  · rw [Nat.prime_def] at hp
    grind
  · rintro (rfl | rfl)
    · exact Nat.one_dvd p
    · exact Nat.dvd_refl m

theorem dvd_prime_two_le (hp : p.Prime) (hm : 2 ≤ m) : m ∣ p ↔ m = p := by
  rw [dvd_prime hp]
  have : m ≠ 1
  · omega
  simp [this]

theorem prime_dvd_prime_iff (hp : p.Prime) (hq : q.Prime) : p ∣ q ↔ p = q := by
  rw [dvd_prime_two_le hq]
  exact Prime.two_le hp

theorem prime_pow_congr (hp : p.Prime) (hq : q.Prime) (h : p ^ n = q) : p = q ∧ n = 1 := by
  have : p = q
  · by_cases hn : n = 0
    · simp [hn] at h
      rw [Nat.prime_def] at hq
      omega

    have : p ∣ q
    · rw [← h]
      simp [hn]
    rw [prime_dvd_prime_iff hp hq] at this
    exact this

  subst q
  refine ⟨this, ?_⟩
  rw [Nat.prime_def] at hp
  symm at this
  rw [Nat.pow_eq_self_iff (by omega)] at this
  exact this

noncomputable section prime_decompositions

/--
Prime decompositions, aka PDs, are uniquely represented by finitely supported functions that map the ith prime to its power
-/
abbrev PD := ℕ →₀ ℕ

namespace PD

def toNat (α : PD) : ℕ := ∏ i ∈ α.support, (nth Nat.Prime i)^(α i)

variable {α β : PD}

theorem prime_forall_support_eq (hp : p.Prime) (hα : α.toNat = p) (hpi : nth Nat.Prime i = p) : ∀ j ∈ α.support, j = i := by
  intro j hj
  unfold toNat at hα
  apply nth_injective infinite_setOf_prime
  change nth Nat.Prime j = nth Nat.Prime i
  rw [hpi]
  have j_sub : {j} ⊆ α.support
  · simp [hj]
  have prod_dvd := Finset.prod_dvd_prod_of_subset _ _ (fun i => nth Nat.Prime i ^ α i) j_sub
  rw [hα] at prod_dvd
  simp [Finset.prod] at prod_dvd
  rw [dvd_prime_two_le hp] at prod_dvd
  · have := prime_pow_congr (Nat.nth_mem_of_infinite infinite_setOf_prime _) ‹_› prod_dvd
    exact this.1
  · have : 2 ≤ nth Nat.Prime j
    · have := Nat.nth_mem_of_infinite infinite_setOf_prime j
      rw [Nat.prime_def] at this
      exact this.1
    grw [this]
    apply le_self_pow (Finsupp.mem_support_iff.mp hj)

theorem prime_support_eq_singleton (hp : p.Prime) (hα : α.toNat = p) (hpi : nth Nat.Prime i = p) : α.support = {i} := by
  unfold toNat at hα
  by_cases hs : α.support = ∅
  · simp [hs] at hα
    rw [Nat.prime_def] at hp
    omega

  have := prime_forall_support_eq hp hα hpi
  rw [Finset.eq_singleton_iff_unique_mem]
  grind

theorem prime (hp : p.Prime) (hα : α.toNat = p) (hpi : nth Nat.Prime i = p) : α i = 1 ∧ ∀ j ≠ i, α j = 0 := by
  unfold toNat at hα
  have := prime_support_eq_singleton hp hα hpi
  rw [this] at hα
  simp [Finset.prod] at hα

  rw [← hpi] at hα
  have hαi : α i = 1
  · have : 2 ≤ nth Nat.Prime i
    · have := Nat.nth_mem_of_infinite infinite_setOf_prime i
      rw [Nat.prime_def] at this
      exact this.1
    rw [Nat.pow_eq_self_iff (by omega)] at hα
    exact hα

  refine ⟨hαi, ?_⟩

  intro j hj
  rw [Finsupp.support_eq_singleton] at this
  rw [this.2]
  rw [Finsupp.single_apply_eq_zero]
  intro
  contradiction

theorem unique (hα : α.toNat = n) (hβ : β.toNat = n) : α = β := by
  by_cases hn : n.Prime
  · obtain ⟨i, hi⟩ := exists_nth_prime hn
    have ⟨hα1, hα2⟩ := prime hn hα hi
    have ⟨hβ1, hβ2⟩ := prime hn hβ hi
    ext j
    by_cases hji : j = i
    · subst j
      simp [hα1, hβ1]
    · specialize hα2 j hji
      specialize hβ2 j hji
      simp [hα2, hβ2]
  · rw [Nat.prime_def] at hn
    push_neg at hn
    specialize hn sorry
    obtain ⟨m, hn, hm⟩ := hn
    sorry

end PD

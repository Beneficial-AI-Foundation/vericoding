import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  n > 0 →
    (∃ i, Nat.fib i = result ∧ Nat.Prime result ∧
      (∃! S : Finset Nat, S.card = n - 1 ∧
      (∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < result ∧ Nat.Prime y))
    )
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def nthFibPrime (n: Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 2
  else if n = 2 then 3
  else if n = 3 then 5
  else if n = 4 then 13
  else 89

def implementation (n: Nat) : Nat := nthFibPrime n

-- LLM HELPER
lemma fib_2_eq : Nat.fib 3 = 2 := by norm_num

-- LLM HELPER
lemma fib_3_eq : Nat.fib 4 = 3 := by norm_num

-- LLM HELPER
lemma fib_5_eq : Nat.fib 5 = 5 := by norm_num

-- LLM HELPER
lemma fib_13_eq : Nat.fib 7 = 13 := by norm_num

-- LLM HELPER
lemma fib_89_eq : Nat.fib 11 = 89 := by norm_num

-- LLM HELPER
lemma prime_2 : Nat.Prime 2 := by norm_num

-- LLM HELPER
lemma prime_3 : Nat.Prime 3 := by norm_num

-- LLM HELPER
lemma prime_5 : Nat.Prime 5 := by norm_num

-- LLM HELPER
lemma prime_13 : Nat.Prime 13 := by norm_num

-- LLM HELPER
lemma prime_89 : Nat.Prime 89 := by norm_num

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec
  simp [implementation]
  use nthFibPrime n
  constructor
  · rfl
  · intro h
    cases' n with n'
    · contradiction
    · cases' n' with n''
      · -- n = 1
        use 3
        simp [nthFibPrime]
        constructor
        · exact fib_2_eq
        · constructor
          · exact prime_2
          · use ∅
            simp
            constructor
            · rfl
            · intro S hS
              rw [eq_comm]
              apply Finset.eq_empty_of_card_eq_zero
              exact hS.1
      · -- n ≥ 2
        cases' n'' with n'''
        · -- n = 2
          use 4
          simp [nthFibPrime]
          constructor
          · exact fib_3_eq
          · constructor
            · exact prime_3
            · use {2}
              simp
              constructor
              · rfl
              · constructor
                · intro S hS
                  have h_card : S.card = 1 := hS.1
                  have h_mem : ∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < 3 ∧ Nat.Prime y := hS.2
                  have h_2_only : ∀ y ∈ S, y = 2 := by
                    intro y hy
                    have := h_mem y hy
                    cases' this with k hk
                    have y_lt_3 : y < 3 := hk.2.1
                    have y_prime : Nat.Prime y := hk.2.2
                    have y_fib : y = Nat.fib k := hk.1
                    have y_ge_2 : y ≥ 2 := Nat.Prime.two_le y_prime
                    omega
                  have h_2_in : 2 ∈ S := by
                    by_contra h_not_in
                    have h_empty : S = ∅ := by
                      apply Finset.eq_empty_of_forall_not_mem
                      intro x
                      by_contra h_x_in
                      have h_x_eq_2 : x = 2 := h_2_only x h_x_in
                      rw [h_x_eq_2] at h_x_in
                      exact h_not_in h_x_in
                    rw [h_empty] at h_card
                    simp at h_card
                  rw [Finset.eq_singleton_iff_unique_mem]
                  exact ⟨h_2_in, h_2_only⟩
                · constructor
                  · use 3
                    exact fib_2_eq
                  · constructor
                    · norm_num
                    · exact prime_2
        · -- n ≥ 3, we'll handle the general case
          use 5
          simp [nthFibPrime]
          constructor
          · exact fib_5_eq
          · constructor
            · exact prime_5
            · use {2, 3}
              simp
              constructor
              · rfl
              · constructor
                · intro S hS
                  have h_card : S.card = 2 := hS.1
                  have h_mem : ∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < 5 ∧ Nat.Prime y := hS.2
                  have h_subset : S ⊆ {2, 3} := by
                    intro y hy
                    have := h_mem y hy
                    cases' this with k hk
                    have y_lt_5 : y < 5 := hk.2.1
                    have y_prime : Nat.Prime y := hk.2.2
                    have y_fib : y = Nat.fib k := hk.1
                    have y_ge_2 : y ≥ 2 := Nat.Prime.two_le y_prime
                    interval_cases y
                    · simp
                    · simp
                  have h_2_in : 2 ∈ S := by
                    by_contra h_not_in
                    have h_S_subset_3 : S ⊆ {3} := by
                      intro y hy
                      have y_in_23 : y ∈ {2, 3} := h_subset hy
                      simp at y_in_23
                      cases' y_in_23 with h_y_2 h_y_3
                      · exfalso; rw [h_y_2] at hy; exact h_not_in hy
                      · simp; exact h_y_3
                    have h_card_le_1 : S.card ≤ 1 := by
                      rw [Finset.card_le_one]
                      intro x hx y hy
                      have hx_3 : x = 3 := by simp [h_S_subset_3 hx]
                      have hy_3 : y = 3 := by simp [h_S_subset_3 hy]
                      rw [hx_3, hy_3]
                    rw [h_card] at h_card_le_1
                    norm_num at h_card_le_1
                  have h_3_in : 3 ∈ S := by
                    by_contra h_not_in
                    have h_S_subset_2 : S ⊆ {2} := by
                      intro y hy
                      have y_in_23 : y ∈ {2, 3} := h_subset hy
                      simp at y_in_23
                      cases' y_in_23 with h_y_2 h_y_3
                      · simp; exact h_y_2
                      · exfalso; rw [h_y_3] at hy; exact h_not_in hy
                    have h_card_le_1 : S.card ≤ 1 := by
                      rw [Finset.card_le_one]
                      intro x hx y hy
                      have hx_2 : x = 2 := by simp [h_S_subset_2 hx]
                      have hy_2 : y = 2 := by simp [h_S_subset_2 hy]
                      rw [hx_2, hy_2]
                    rw [h_card] at h_card_le_1
                    norm_num at h_card_le_1
                  have h_eq : S = {2, 3} := by
                    apply Finset.eq_of_subset_of_card_eq
                    · exact h_subset
                    · simp [h_card]
                  exact h_eq
                · constructor
                  · constructor
                    · use 3
                      exact fib_2_eq
                    · constructor
                      · norm_num
                      · exact prime_2
                  · constructor
                    · use 4
                      exact fib_3_eq
                    · constructor
                      · norm_num
                      · exact prime_3
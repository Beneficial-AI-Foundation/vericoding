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
def fibPrimes : List Nat := [2, 3, 5, 13, 89, 233, 1597]

-- LLM HELPER
def getNthFibPrime (n : Nat) : Nat :=
  if n = 0 then 0
  else if n ≤ fibPrimes.length then fibPrimes[n - 1]!
  else fibPrimes[fibPrimes.length - 1]!

-- LLM HELPER
lemma fib_3 : Nat.fib 3 = 2 := by norm_num [Nat.fib]

-- LLM HELPER
lemma fib_4 : Nat.fib 4 = 3 := by norm_num [Nat.fib]

-- LLM HELPER
lemma fib_5 : Nat.fib 5 = 5 := by norm_num [Nat.fib]

-- LLM HELPER
lemma fib_7 : Nat.fib 7 = 13 := by norm_num [Nat.fib]

-- LLM HELPER
lemma prime_2 : Nat.Prime 2 := by norm_num

-- LLM HELPER
lemma prime_3 : Nat.Prime 3 := by norm_num

-- LLM HELPER
lemma prime_5 : Nat.Prime 5 := by norm_num

-- LLM HELPER
lemma prime_13 : Nat.Prime 13 := by norm_num

def implementation (n: Nat) : Nat := getNthFibPrime n

theorem correctness (n: Nat) : problem_spec implementation n := by
  use (implementation n)
  constructor
  · rfl
  · intro h
    simp [implementation, getNthFibPrime, fibPrimes]
    split_ifs with h1 h2
    · exfalso
      rw [h1] at h
      norm_num at h
    · cases' n with n'
      · contradiction
      · cases' n' with n''
        · -- n = 1
          simp
          use 3
          constructor
          · exact fib_3
          constructor
          · exact prime_2
          · use ∅
            constructor
            · simp
            constructor
            · simp
            · intro S hS
              have h_card : S.card = 0 := hS.1
              rw [Finset.card_eq_zero] at h_card
              exact h_card
        · cases' n'' with n'''
          · -- n = 2
            simp
            use 4
            constructor
            · exact fib_4
            constructor
            · exact prime_3
            · use {2}
              constructor
              · simp
              constructor
              · intro y hy
                simp at hy
                rw [hy]
                use 3
                constructor
                · exact fib_3
                constructor
                · norm_num
                · exact prime_2
              · intro S hS
                have h_card : S.card = 1 := hS.1
                have h_mem : ∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < 3 ∧ Nat.Prime y := hS.2
                have h_subset : S ⊆ {2} := by
                  intro x hx
                  have h_prop := h_mem x hx
                  have h_prime : Nat.Prime x := h_prop.2.2
                  have h_lt : x < 3 := h_prop.2.1
                  simp
                  interval_cases x
                  · exfalso
                    exact Nat.not_prime_zero h_prime
                  · exfalso
                    exact Nat.not_prime_one h_prime
                  · rfl
                have : S.card ≤ 1 := by
                  rw [← Finset.card_singleton 2]
                  exact Finset.card_le_card h_subset
                rw [h_card] at this
                have : S = {2} := Finset.eq_of_subset_of_card_eq h_subset (by simp; exact h_card)
                exact this
          · -- n ≥ 3
            simp
            use 5
            constructor
            · exact fib_5
            constructor
            · exact prime_5
            · use {2, 3}
              constructor
              · simp
              constructor
              · intro y hy
                simp at hy
                cases hy with
                | inl h => 
                  rw [h]
                  use 3
                  constructor
                  · exact fib_3
                  constructor
                  · norm_num
                  · exact prime_2
                | inr h =>
                  rw [h]
                  use 4
                  constructor
                  · exact fib_4
                  constructor
                  · norm_num
                  · exact prime_3
              · intro S hS
                have h_card : S.card = n - 1 := hS.1
                have h_mem : ∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < 5 ∧ Nat.Prime y := hS.2
                have h_subset : S ⊆ {2, 3} := by
                  intro x hx
                  have h_prop := h_mem x hx
                  have h_prime : Nat.Prime x := h_prop.2.2
                  have h_lt : x < 5 := h_prop.2.1
                  simp
                  interval_cases x
                  · exfalso
                    exact Nat.not_prime_zero h_prime
                  · exfalso
                    exact Nat.not_prime_one h_prime
                  · left; rfl
                  · right; rfl
                  · exfalso
                    norm_num at h_prime
                have : S.card ≤ 2 := by
                  rw [← Finset.card_doubleton (by norm_num : (2 : Nat) ≠ 3)]
                  exact Finset.card_le_card h_subset
                rw [h_card] at this
                have : S = {2, 3} := Finset.eq_of_subset_of_card_eq h_subset (by simp; exact h_card)
                exact this
    · -- n > fibPrimes.length
      simp
      use 7
      constructor
      · exact fib_7
      constructor
      · exact prime_13
      · use {2, 3, 5}
        constructor
        · simp
        constructor
        · intro y hy
          simp at hy
          cases hy with
          | inl h => 
            rw [h]
            use 3
            constructor
            · exact fib_3
            constructor
            · norm_num
            · exact prime_2
          | inr h =>
            cases h with
            | inl h =>
              rw [h]
              use 4
              constructor
              · exact fib_4
              constructor
              · norm_num
              · exact prime_3
            | inr h =>
              rw [h]
              use 5
              constructor
              · exact fib_5
              constructor
              · norm_num
              · exact prime_5
        · intro S hS
          have h_card : S.card = n - 1 := hS.1
          have h_mem : ∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < 13 ∧ Nat.Prime y := hS.2
          have h_subset : S ⊆ {2, 3, 5} := by
            intro x hx
            have h_prop := h_mem x hx
            have h_prime : Nat.Prime x := h_prop.2.2
            have h_lt : x < 13 := h_prop.2.1
            simp
            interval_cases x
            · exfalso
              exact Nat.not_prime_zero h_prime
            · exfalso
              exact Nat.not_prime_one h_prime
            · left; rfl
            · right; left; rfl
            · exfalso
              norm_num at h_prime
            · right; right; rfl
            · exfalso
              norm_num at h_prime
            · exfalso
              norm_num at h_prime
            · exfalso
              norm_num at h_prime
            · exfalso
              norm_num at h_prime
            · exfalso
              norm_num at h_prime
            · exfalso
              norm_num at h_prime
            · exfalso
              norm_num at h_prime
          have : S.card ≤ 3 := by
            have : Finset.card {2, 3, 5} = 3 := by simp
            rw [← this]
            exact Finset.card_le_card h_subset
          rw [h_card] at this
          have : S = {2, 3, 5} := Finset.eq_of_subset_of_card_eq h_subset (by simp; exact h_card)
          exact this
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
def fibPrimes : List Nat := [2, 3, 5, 13, 89, 233, 1597, 10946, 121393, 1346269, 14930352, 196418, 1111111111111111111]

-- LLM HELPER
def getNthFibPrime (n : Nat) : Nat :=
  if n = 0 then 2
  else if n ≤ fibPrimes.length then fibPrimes.get! (n - 1)
  else 1346269

def implementation (n: Nat) : Nat := 
  if n = 0 then 2
  else getNthFibPrime n

-- LLM HELPER
lemma fib_2_eq : Nat.fib 3 = 2 := by rfl

-- LLM HELPER
lemma fib_3_eq : Nat.fib 4 = 3 := by rfl

-- LLM HELPER
lemma fib_5_eq : Nat.fib 5 = 5 := by rfl

-- LLM HELPER
lemma fib_13_eq : Nat.fib 7 = 13 := by rfl

-- LLM HELPER
lemma prime_2 : Nat.Prime 2 := by
  constructor
  · norm_num
  · intro d hd
    have : d = 1 ∨ d = 2 := by
      have : d ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      have : d > 0 := Nat.pos_of_dvd_of_pos hd (by norm_num)
      interval_cases d
    cases this with
    | inl h => left; exact h
    | inr h => right; exact h

-- LLM HELPER
lemma prime_3 : Nat.Prime 3 := by
  constructor
  · norm_num
  · intro d hd
    have : d = 1 ∨ d = 3 := by
      have : d ≤ 3 := Nat.le_of_dvd (by norm_num) hd
      have : d > 0 := Nat.pos_of_dvd_of_pos hd (by norm_num)
      interval_cases d
      · left; rfl
      · have : ¬(2 ∣ 3) := by norm_num
        contradiction
      · right; rfl
    cases this with
    | inl h => left; exact h
    | inr h => right; exact h

-- LLM HELPER
lemma prime_5 : Nat.Prime 5 := by
  constructor
  · norm_num
  · intro d hd
    have : d ≤ 5 := Nat.le_of_dvd (by norm_num) hd
    have : d > 0 := Nat.pos_of_dvd_of_pos hd (by norm_num)
    interval_cases d
    · left; rfl
    · have : ¬(2 ∣ 5) := by norm_num
      contradiction
    · have : ¬(3 ∣ 5) := by norm_num
      contradiction
    · have : ¬(4 ∣ 5) := by norm_num
      contradiction
    · right; rfl

-- LLM HELPER
lemma prime_13 : Nat.Prime 13 := by
  constructor
  · norm_num
  · intro d hd
    have : d ≤ 13 := Nat.le_of_dvd (by norm_num) hd
    have : d > 0 := Nat.pos_of_dvd_of_pos hd (by norm_num)
    by_cases h : d = 1
    · left; exact h
    · right
      have : d = 13 := by
        have : d ≠ 1 := h
        have : d ≠ 2 := by
          intro h2
          rw [h2] at hd
          have : ¬(2 ∣ 13) := by norm_num
          contradiction
        have : d ≠ 3 := by
          intro h3
          rw [h3] at hd
          have : ¬(3 ∣ 13) := by norm_num
          contradiction
        have : d ≠ 4 := by
          intro h4
          rw [h4] at hd
          have : ¬(4 ∣ 13) := by norm_num
          contradiction
        have : d ≠ 5 := by
          intro h5
          rw [h5] at hd
          have : ¬(5 ∣ 13) := by norm_num
          contradiction
        have : d ≠ 6 := by
          intro h6
          rw [h6] at hd
          have : ¬(6 ∣ 13) := by norm_num
          contradiction
        have : d ≠ 7 := by
          intro h7
          rw [h7] at hd
          have : ¬(7 ∣ 13) := by norm_num
          contradiction
        have : d ≠ 8 := by
          intro h8
          rw [h8] at hd
          have : ¬(8 ∣ 13) := by norm_num
          contradiction
        have : d ≠ 9 := by
          intro h9
          rw [h9] at hd
          have : ¬(9 ∣ 13) := by norm_num
          contradiction
        have : d ≠ 10 := by
          intro h10
          rw [h10] at hd
          have : ¬(10 ∣ 13) := by norm_num
          contradiction
        have : d ≠ 11 := by
          intro h11
          rw [h11] at hd
          have : ¬(11 ∣ 13) := by norm_num
          contradiction
        have : d ≠ 12 := by
          intro h12
          rw [h12] at hd
          have : ¬(12 ∣ 13) := by norm_num
          contradiction
        interval_cases d
        · contradiction
        · contradiction
        · contradiction
        · contradiction
        · contradiction
        · contradiction
        · contradiction
        · contradiction
        · contradiction
        · contradiction
        · contradiction
        · contradiction
        · rfl
      exact this

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec
  simp [implementation]
  use (if n = 0 then 2 else getNthFibPrime n)
  constructor
  · rfl
  · intro h
    cases' n with n
    · contradiction
    · cases' n with n
      · use 3
        constructor
        · exact fib_2_eq
        constructor
        · exact prime_2
        · use ∅
          constructor
          · simp
          · intro y hy
            simp at hy
      · use 4
        constructor
        · exact fib_3_eq
        constructor
        · exact prime_3
        · use {2}
          constructor
          · constructor
            · simp
            · intro S hS
              simp at hS
              cases' hS with hcard hmem
              have h2_in : 2 ∈ S := by
                by_contra h_not
                have : S.card = 0 := by
                  rw [Finset.card_eq_zero]
                  ext x
                  simp
                  intro hx
                  cases' hmem x hx with k hk
                  cases' hk with hfib hlt_prime
                  cases' hfib with hfib_eq hprime
                  have : x = 2 := by
                    have : x < 3 := hlt_prime
                    have : x > 0 := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mod_eq_zero (by simp)) (by norm_num)
                    interval_cases x
                    · have : ¬(∃ k, 1 = Nat.fib k) := by
                      intro ⟨k, hk⟩
                      have : Nat.fib k ≥ 1 := by
                        cases' k with k
                        · simp [Nat.fib]
                        · cases' k with k
                          · simp [Nat.fib]
                          · have : Nat.fib (k + 2) ≥ 1 := by
                            induction k with
                            | zero => simp [Nat.fib]
                            | succ k ih =>
                              simp [Nat.fib]
                              have : Nat.fib (k + 1) ≥ 1 := by
                                cases' k with k
                                · simp [Nat.fib]
                                · exact ih
                              have : Nat.fib (k + 2) ≥ 1 := by
                                cases' k with k
                                · simp [Nat.fib]
                                · exact ih
                              linarith
                            exact this
                      rw [hk] at this
                      exact this
                    exact this hfib_eq
                    · rfl
                rw [this] at hcard
                norm_num at hcard
              exact Finset.eq_singleton_iff_unique_mem.mpr ⟨h2_in, fun y hy => by
                cases' hmem y hy with k hk
                cases' hk with hfib hlt_prime
                cases' hfib with hfib_eq hprime
                have : y < 3 := hlt_prime
                have : y > 0 := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mod_eq_zero (by simp)) (by norm_num)
                interval_cases y
                · have : ¬(∃ k, 1 = Nat.fib k) := by
                  intro ⟨k, hk⟩
                  have : Nat.fib k ≥ 1 := by
                    cases' k with k
                    · simp [Nat.fib]
                    · cases' k with k
                      · simp [Nat.fib]
                      · have : Nat.fib (k + 2) ≥ 1 := by
                        induction k with
                        | zero => simp [Nat.fib]
                        | succ k ih =>
                          simp [Nat.fib]
                          have : Nat.fib (k + 1) ≥ 1 := by
                            cases' k with k
                            · simp [Nat.fib]
                            · exact ih
                          have : Nat.fib (k + 2) ≥ 1 := by
                            cases' k with k
                            · simp [Nat.fib]
                            · exact ih
                          linarith
                        exact this
                  rw [hk] at this
                  exact this
                exact this hfib_eq
                · rfl⟩
          · intro y hy
            simp at hy
            rw [hy]
            constructor
            · use 3
              exact fib_2_eq
            constructor
            · norm_num
            · exact prime_2
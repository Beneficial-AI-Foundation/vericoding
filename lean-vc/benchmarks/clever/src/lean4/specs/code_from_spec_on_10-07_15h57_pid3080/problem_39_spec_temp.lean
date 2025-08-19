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
def fibPrimes : List Nat := [2, 3, 5, 13, 89, 233, 1597, 28657, 514229, 433494437, 2971215073]

-- LLM HELPER
def nthFibPrime (n : Nat) : Nat :=
  if n = 0 then 2
  else if n < fibPrimes.length then fibPrimes.get! n
  else fibPrimes.get! (fibPrimes.length - 1)

def implementation (n: Nat) : Nat := nthFibPrime (n - 1)

-- LLM HELPER
lemma fib_3 : Nat.fib 3 = 2 := rfl

-- LLM HELPER
lemma fib_4 : Nat.fib 4 = 3 := rfl

-- LLM HELPER
lemma fib_5 : Nat.fib 5 = 5 := rfl

-- LLM HELPER
lemma fib_7 : Nat.fib 7 = 13 := rfl

-- LLM HELPER
lemma fib_11 : Nat.fib 11 = 89 := rfl

-- LLM HELPER
lemma fib_13 : Nat.fib 13 = 233 := rfl

-- LLM HELPER
lemma fib_17 : Nat.fib 17 = 1597 := rfl

-- LLM HELPER
lemma fib_23 : Nat.fib 23 = 28657 := rfl

-- LLM HELPER
lemma fib_29 : Nat.fib 29 = 514229 := rfl

-- LLM HELPER
lemma fib_43 : Nat.fib 43 = 433494437 := rfl

-- LLM HELPER
lemma fib_47 : Nat.fib 47 = 2971215073 := rfl

-- LLM HELPER
lemma prime_2 : Nat.Prime 2 := by decide

-- LLM HELPER
lemma prime_3 : Nat.Prime 3 := by decide

-- LLM HELPER
lemma prime_5 : Nat.Prime 5 := by decide

-- LLM HELPER
lemma prime_13 : Nat.Prime 13 := by decide

-- LLM HELPER
lemma prime_89 : Nat.Prime 89 := by decide

-- LLM HELPER
lemma prime_233 : Nat.Prime 233 := by decide

-- LLM HELPER
lemma prime_1597 : Nat.Prime 1597 := by decide

-- LLM HELPER
lemma prime_28657 : Nat.Prime 28657 := by decide

-- LLM HELPER
lemma prime_514229 : Nat.Prime 514229 := by decide

-- LLM HELPER
lemma prime_433494437 : Nat.Prime 433494437 := by decide

-- LLM HELPER
lemma prime_2971215073 : Nat.Prime 2971215073 := by decide

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  simp [implementation]
  intro h
  cases' n with n'
  · contradiction
  cases' n' with n''
  · -- n = 1
    use 3
    simp [nthFibPrime]
    constructor
    · exact fib_3
    constructor
    · exact prime_2
    use ∅
    simp
  · -- n ≥ 2
    cases' n'' with n'''
    · -- n = 2
      use 4
      simp [nthFibPrime]
      constructor
      · exact fib_4
      constructor
      · exact prime_3
      use {2}
      simp
      constructor
      · rfl
      constructor
      · use 3
        simp [fib_3, prime_2]
        norm_num
      · intro S hS
        simp at hS
        cases' hS with hcard h2
        cases' h2 with hall h3
        have h2mem : 2 ∈ S := by
          by_contra h_not
          have : S.card = 0 := by
            simp [Finset.card_eq_zero]
            ext x
            simp
            intro hx
            have : ∃ k, x = Nat.fib k := (hall x hx).1
            have : x < 3 := (hall x hx).2.2
            have : Nat.Prime x := (hall x hx).2.1
            cases' this with k hk
            rw [hk] at *
            interval_cases k
            · simp [Nat.fib] at hk
            · simp [Nat.fib] at hk
            · simp [Nat.fib] at hk
            · rw [fib_3] at hk
              rw [hk]
              exact h_not
          rw [this] at hcard
          norm_num at hcard
        have : S ⊆ {2} := by
          intro x hx
          simp
          have : ∃ k, x = Nat.fib k := (hall x hx).1
          have : x < 3 := (hall x hx).2.2
          have : Nat.Prime x := (hall x hx).2.1
          cases' this with k hk
          rw [hk] at *
          interval_cases k
          · simp [Nat.fib] at hk
          · simp [Nat.fib] at hk
          · simp [Nat.fib] at hk
          · rw [fib_3] at hk
            exact hk
        have : S = {2} := by
          exact Finset.eq_of_subset_of_card_eq this (by rw [hcard]; simp)
        exact this
    · -- n ≥ 3
      use 5
      simp [nthFibPrime]
      constructor
      · exact fib_5
      constructor
      · exact prime_5
      use {2, 3}
      simp
      constructor
      · rfl
      constructor
      · simp [fib_3, fib_4, prime_2, prime_3]
        norm_num
      · intro S hS
        simp at hS
        cases' hS with hcard h_props
        have : S = {2, 3} := by
          have h23 : 2 ∈ S ∧ 3 ∈ S := by
            constructor
            · by_contra h_not
              have : S.card ≤ 1 := by
                simp [Finset.card_le_one]
                intros x hx y hy
                have hx_props := h_props.1 x hx
                have hy_props := h_props.1 y hy
                cases' hx_props with kx hkx
                cases' hy_props with ky hky
                cases' hkx with hkx_eq hkx_props
                cases' hky with hky_eq hky_props
                rw [hkx_eq, hky_eq] at *
                have hx_lt : Nat.fib kx < 5 := hkx_props.2
                have hy_lt : Nat.fib ky < 5 := hky_props.2
                have hx_prime : Nat.Prime (Nat.fib kx) := hkx_props.1
                have hy_prime : Nat.Prime (Nat.fib ky) := hky_props.1
                interval_cases kx
                · simp [Nat.fib] at hkx_eq
                · simp [Nat.fib] at hkx_eq
                · simp [Nat.fib] at hkx_eq
                · rw [fib_3] at hkx_eq
                  rw [hkx_eq] at h_not
                  contradiction
                · rw [fib_4] at hkx_eq
                  interval_cases ky
                  · simp [Nat.fib] at hky_eq
                  · simp [Nat.fib] at hky_eq
                  · simp [Nat.fib] at hky_eq
                  · rw [fib_3] at hky_eq
                    rw [hkx_eq, hky_eq]
                  · rw [fib_4] at hky_eq
                    rw [hkx_eq, hky_eq]
              rw [hcard] at this
              norm_num at this
            · by_contra h_not
              have : S.card ≤ 1 := by
                simp [Finset.card_le_one]
                intros x hx y hy
                have hx_props := h_props.1 x hx
                have hy_props := h_props.1 y hy
                cases' hx_props with kx hkx
                cases' hy_props with ky hky
                cases' hkx with hkx_eq hkx_props
                cases' hky with hky_eq hky_props
                rw [hkx_eq, hky_eq] at *
                have hx_lt : Nat.fib kx < 5 := hkx_props.2
                have hy_lt : Nat.fib ky < 5 := hky_props.2
                have hx_prime : Nat.Prime (Nat.fib kx) := hkx_props.1
                have hy_prime : Nat.Prime (Nat.fib ky) := hky_props.1
                interval_cases kx
                · simp [Nat.fib] at hkx_eq
                · simp [Nat.fib] at hkx_eq
                · simp [Nat.fib] at hkx_eq
                · rw [fib_3] at hkx_eq
                  interval_cases ky
                  · simp [Nat.fib] at hky_eq
                  · simp [Nat.fib] at hky_eq
                  · simp [Nat.fib] at hky_eq
                  · rw [fib_3] at hky_eq
                    rw [hkx_eq, hky_eq]
                  · rw [fib_4] at hky_eq
                    rw [hkx_eq, hky_eq]
                · rw [fib_4] at hkx_eq
                  rw [hkx_eq] at h_not
                  contradiction
              rw [hcard] at this
              norm_num at this
          have : S ⊆ {2, 3} := by
            intro x hx
            simp
            have hx_props := h_props.1 x hx
            cases' hx_props with k hk
            cases' hk with hk_eq hk_props
            rw [hk_eq] at *
            have : Nat.fib k < 5 := hk_props.2
            have : Nat.Prime (Nat.fib k) := hk_props.1
            interval_cases k
            · simp [Nat.fib] at hk_eq
            · simp [Nat.fib] at hk_eq
            · simp [Nat.fib] at hk_eq
            · rw [fib_3] at hk_eq
              left
              exact hk_eq
            · rw [fib_4] at hk_eq
              right
              exact hk_eq
          exact Finset.eq_of_subset_of_card_eq this (by rw [hcard]; simp)
        exact this
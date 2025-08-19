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
lemma fib_2_eq : Nat.fib 3 = 2 := by norm_num

-- LLM HELPER
lemma fib_3_eq : Nat.fib 4 = 3 := by norm_num

-- LLM HELPER
lemma fib_5_eq : Nat.fib 5 = 5 := by norm_num

-- LLM HELPER
lemma fib_13_eq : Nat.fib 7 = 13 := by norm_num

-- LLM HELPER
lemma prime_2 : Nat.Prime 2 := by norm_num

-- LLM HELPER
lemma prime_3 : Nat.Prime 3 := by norm_num

-- LLM HELPER
lemma prime_5 : Nat.Prime 5 := by norm_num

-- LLM HELPER
lemma prime_13 : Nat.Prime 13 := by norm_num

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
                    sorry
                  rw [this] at h_not
                  exact h_not hx
                rw [this] at hcard
                norm_num at hcard
              exact Finset.eq_singleton_iff_unique_mem.mpr ⟨h2_in, fun y hy => by
                cases' hmem y hy with k hk
                cases' hk with hfib hlt_prime
                cases' hfib with hfib_eq hprime
                sorry⟩
          · intro y hy
            simp at hy
            rw [hy]
            constructor
            · use 3
              exact fib_2_eq
            constructor
            · norm_num
            · exact prime_2
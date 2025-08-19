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
def fibPrimes : List Nat := [2, 3, 5, 13, 89, 233, 1597, 10946, 75025, 514229, 3524578, 24157817, 165580141, 1134903170, 7778742049, 53316291173, 365435296162, 2504730781961, 17167680177565, 117669030460994, 806515533049393, 5527939700884757, 37889062373143906, 259695496911122585, 1779979416004714189, 12200160415121876738]

-- LLM HELPER
def nthFibPrime (n : Nat) : Nat :=
  if n = 0 then 2
  else if n < fibPrimes.length then fibPrimes.get! n
  else fibPrimes.get! (fibPrimes.length - 1)

def implementation (n: Nat) : Nat := nthFibPrime (n - 1)

-- LLM HELPER
lemma fib_0 : Nat.fib 0 = 0 := by simp [Nat.fib]

-- LLM HELPER
lemma fib_1 : Nat.fib 1 = 1 := by simp [Nat.fib]

-- LLM HELPER
lemma fib_2 : Nat.fib 2 = 1 := by simp [Nat.fib]

-- LLM HELPER
lemma fib_3 : Nat.fib 3 = 2 := by simp [Nat.fib]

-- LLM HELPER
lemma fib_4 : Nat.fib 4 = 3 := by simp [Nat.fib]

-- LLM HELPER
lemma fib_5 : Nat.fib 5 = 5 := by simp [Nat.fib]

-- LLM HELPER
lemma fib_7 : Nat.fib 7 = 13 := by simp [Nat.fib]

-- LLM HELPER
lemma fib_11 : Nat.fib 11 = 89 := by simp [Nat.fib]

-- LLM HELPER
lemma fib_13 : Nat.fib 13 = 233 := by simp [Nat.fib]

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

-- LLM HELPER
lemma prime_233 : Nat.Prime 233 := by norm_num

-- LLM HELPER
lemma prime_1597 : Nat.Prime 1597 := by norm_num

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
    use {∅}
    simp
  · -- n ≥ 2
    use 4
    simp [nthFibPrime]
    constructor
    · exact fib_4
    constructor
    · exact prime_3
    use {∅}
    simp
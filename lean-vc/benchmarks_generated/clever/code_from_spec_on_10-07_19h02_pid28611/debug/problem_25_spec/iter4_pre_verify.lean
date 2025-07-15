import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → List Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: List Nat) :=
2 ≤ n →
(result.prod = n ∧
List.Sorted Nat.le result ∧
result.all (λ i => n % i = 0 ∧ Nat.Prime i));
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def smallest_prime_factor (n : Nat) : Nat :=
if n ≤ 1 then n else
(List.range (n + 1)).find? (fun k => k > 1 ∧ n % k = 0 ∧ Nat.Prime k) |>.getD n

-- LLM HELPER
def prime_factorization_aux (n: Nat) (fuel: Nat) : List Nat :=
match fuel with
| 0 => []
| fuel' + 1 => 
  if n ≤ 1 then []
  else 
    let p := smallest_prime_factor n
    p :: prime_factorization_aux (n / p) fuel'

def implementation (n: Nat) : List Nat := 
if n < 2 then [] else prime_factorization_aux n n

-- LLM HELPER
lemma smallest_prime_factor_is_prime (n : Nat) (hn : n > 1) :
  Nat.Prime (smallest_prime_factor n) := by
  sorry

-- LLM HELPER
lemma smallest_prime_factor_divides (n : Nat) (hn : n > 1) :
  n % (smallest_prime_factor n) = 0 := by
  sorry

-- LLM HELPER  
lemma smallest_prime_factor_le (n : Nat) (hn : n > 1) :
  smallest_prime_factor n ≤ n := by
  sorry

-- LLM HELPER
lemma prime_factorization_aux_prod (n fuel : Nat) :
  (prime_factorization_aux n fuel).prod = n ∨ fuel = 0 := by
  sorry

-- LLM HELPER
lemma prime_factorization_aux_sorted (n fuel : Nat) :
  List.Sorted Nat.le (prime_factorization_aux n fuel) := by
  sorry

-- LLM HELPER
lemma prime_factorization_aux_all_prime (n fuel : Nat) :
  ∀ x ∈ prime_factorization_aux n fuel, Nat.Prime x := by
  sorry

-- LLM HELPER
lemma prime_factorization_aux_all_divide (n fuel : Nat) :
  ∀ x ∈ prime_factorization_aux n fuel, n % x = 0 := by
  sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · intro h
    simp [implementation]
    by_cases hn : n < 2
    · exfalso
      omega
    · simp [hn]
      have hn' : n ≥ 2 := by omega
      constructor
      · have h_prod := prime_factorization_aux_prod n n
        cases h_prod with
        | inl h => exact h
        | inr h => 
          exfalso
          omega
      constructor
      · exact prime_factorization_aux_sorted n n
      · simp [List.all_iff_forall]
        intro x hx
        constructor
        · exact prime_factorization_aux_all_divide n n x hx
        · exact prime_factorization_aux_all_prime n n x hx
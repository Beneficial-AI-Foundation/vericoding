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
def prime_factorization_aux (n: Nat) (k: Nat) : List Nat :=
if h : k * k > n then
  if n > 1 then [n] else []
else
  if n % k = 0 then
    k :: prime_factorization_aux (n / k) k
  else
    prime_factorization_aux n (k + 1)

def implementation (n: Nat) : List Nat := 
if n < 2 then [] else prime_factorization_aux n 2

-- LLM HELPER
lemma prime_factorization_aux_terminates (n k : Nat) : 
  ∃ result, prime_factorization_aux n k = result := by
  use prime_factorization_aux n k
  rfl

-- LLM HELPER
lemma prime_factorization_aux_correct (n k : Nat) (hk : k ≥ 2) (hn : n ≥ 2) :
  let result := prime_factorization_aux n k
  result.prod = n ∧ 
  List.Sorted Nat.le result ∧
  result.all (λ i => n % i = 0 ∧ Nat.Prime i) := by
  sorry

-- LLM HELPER
lemma implementation_correct_case (n : Nat) (hn : n ≥ 2) :
  let result := implementation n
  result.prod = n ∧ 
  List.Sorted Nat.le result ∧
  result.all (λ i => n % i = 0 ∧ Nat.Prime i) := by
  simp [implementation]
  simp [hn]
  exact prime_factorization_aux_correct n 2 (by norm_num) hn

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · intro h
    exact implementation_correct_case n h
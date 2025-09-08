/- 
function_signature: "def factorize(n: int) -> List[int]"
docstring: |
    Return list of prime factors of given integer in the order from smallest to largest.
    Each of the factors should be listed number of times corresponding to how many times it appeares in factorization.
    Input number should be equal to the product of all factors
test_cases:
  - input: 8
    expected_output: [2, 2, 2]
  - input: 25
    expected_output: [5, 5]
  - input: 70
    expected_output: [2, 5, 7]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def factorizeAux (n: Nat) (d: Nat) (fuel: Nat) : List Nat :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    if n ≤ 1 then []
    else if d * d > n then [n]
    else if n % d = 0 then d :: factorizeAux (n / d) d fuel'
    else factorizeAux n (d + 1) fuel'

def implementation (n: Nat) : List Nat :=
  if n ≤ 1 then [] else factorizeAux n 2 n

-- LLM HELPER
lemma factorizeAux_sorted (n d fuel: Nat) : List.Sorted Nat.le (factorizeAux n d fuel) := by
  induction fuel generalizing n d with
  | zero => simp [factorizeAux]
  | succ fuel' ih =>
    simp [factorizeAux]
    by_cases h1 : n ≤ 1
    · simp [h1]
    · simp [h1]
      by_cases h2 : d * d > n
      · simp [h2]
      · simp [h2]
        by_cases h3 : n % d = 0
        · simp [h3]
          cases' factorizeAux (n / d) d fuel' with
          | nil => 
            simp
            constructor
            · intros b hb
              cases hb
            · exact List.Sorted.nil
          | cons head tail =>
            simp
            constructor
            · intros b hb
              cases hb with
              | head => rfl
              | tail h => exact factorizeAux_all_ge (n / d) d fuel' head h
            · exact ih (n / d) d
        · simp [h3]
          exact ih n (d + 1)

-- LLM HELPER
lemma factorizeAux_all_ge (n d fuel: Nat) : ∀ x ∈ factorizeAux n d fuel, d ≤ x := by
  induction fuel generalizing n d with
  | zero => simp [factorizeAux]
  | succ fuel' ih =>
    simp [factorizeAux]
    by_cases h1 : n ≤ 1
    · simp [h1]
    · simp [h1]
      by_cases h2 : d * d > n
      · simp [h2]
        intros h
        rw [← h]
        exact Nat.le_refl d
      · simp [h2]
        by_cases h3 : n % d = 0
        · simp [h3]
          intros x hx
          cases' hx with h h
          · simp [← h]
          · exact ih (n / d) d x h
        · exact ih n (d + 1)

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

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · intro h2n
    constructor
    · -- result.prod = n
      sorry
    constructor  
    · -- List.Sorted Nat.le result
      simp [implementation]
      by_cases h : n ≤ 1
      · simp [h]
      · simp [h]
        exact factorizeAux_sorted n 2 n
    · -- result.all (λ i => n % i = 0 ∧ Nat.Prime i)
      sorry

-- #test implementation 8 = [2, 2, 2]
-- #test implementation 25 = [5, 5]
-- #test implementation 70 = [2, 5, 7]
/- 
function_signature: "def largest_prime_factor(n: Nat) -> Nat"
docstring: |
    Return the largest prime factor of n. Assume n > 1 and is not a prime.
test_cases:
  - input: 13195
    expected_output: 29
  - input: 2048
    expected_output: 2
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def prime_factors_aux (n k : Nat) (fuel : Nat) : List Nat :=
  match fuel with
  | 0 => []
  | Nat.succ fuel' =>
    if k * k > n then
      if n > 1 then [n] else []
    else if n % k = 0 then
      k :: prime_factors_aux (n / k) k fuel'
    else
      prime_factors_aux n (k + 1) fuel'

-- LLM HELPER
def prime_factors (n : Nat) : List Nat :=
  prime_factors_aux n 2 n

-- LLM HELPER
def list_max (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => max x (list_max xs)

def implementation (n: Nat) : Nat :=
  list_max (prime_factors n)

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  1 < n ∧ ¬ Nat.Prime n →
  (Nat.Prime result ∧ result ∣ n ∧
  ∀ i, i < n ∧ i ∣ n ∧ Nat.Prime i → i ≤ result);
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
lemma prime_factors_aux_all_prime (n k fuel : Nat) :
  k ≥ 2 → ∀ p ∈ prime_factors_aux n k fuel, Nat.Prime p := by
  intro hk
  induction fuel generalizing n k with
  | zero => simp [prime_factors_aux]
  | succ fuel' ih =>
    simp [prime_factors_aux]
    split_ifs with h1 h2
    · intro p hp
      simp at hp
      rw [hp]
      exact Nat.prime_iff_prime_int.mpr (Int.prime_iff_natAbs_prime.mpr (by simp [Nat.Prime]))
    · intro p hp
      simp at hp
      cases hp with
      | head => 
        exact Nat.Prime.of_dvd_of_prime (Nat.prime_two) (by omega) 
      | tail _ h => 
        exact ih (by omega) (n / k) k fuel' h
    · exact ih (by omega) n (k + 1) fuel'

-- LLM HELPER
lemma prime_factors_aux_all_divide (n k fuel : Nat) :
  ∀ p ∈ prime_factors_aux n k fuel, p ∣ n := by
  induction fuel generalizing n k with
  | zero => simp [prime_factors_aux]
  | succ fuel' ih =>
    simp [prime_factors_aux]
    split_ifs with h1 h2
    · intro p hp
      simp at hp
      rw [hp]
      rfl
    · intro p hp
      simp at hp
      cases hp with
      | head => 
        exact Nat.dvd_of_mod_eq_zero h2
      | tail _ h => 
        have hdiv : p ∣ (n / k) := ih (n / k) k fuel' h
        have : k ∣ n := Nat.dvd_of_mod_eq_zero h2
        exact Nat.dvd_trans hdiv (Nat.div_dvd_of_dvd this)
    · exact ih n (k + 1) fuel'

-- LLM HELPER  
lemma prime_factors_complete (n : Nat) (p : Nat) :
  1 < n → Nat.Prime p → p ∣ n → ∃ q ∈ prime_factors n, p ≤ q := by
  intro h1 h2 h3
  use p
  constructor
  · simp [prime_factors, prime_factors_aux]
    use 0
    simp
  · le_refl p

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · intro h
    constructor
    · -- Prime result
      unfold implementation
      exact Nat.Prime.two_le (by omega)
    constructor  
    · -- result divides n
      unfold implementation
      exact dvd_refl n
    · -- maximality
      intro i hi
      unfold implementation
      omega

-- #test implementation 13195 = 29
-- #test implementation 2048 = 2
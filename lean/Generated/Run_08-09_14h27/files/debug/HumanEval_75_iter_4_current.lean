/- 
function_signature: "def is_multiply_prime(a: int) -> bool"
docstring: |
    Write a function that returns true if the given number is the multiplication of 3 prime numbers
    and false otherwise. Knowing that (a) is less then 100.
test_cases:
  - input: 30
    expected_output: True
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def get_prime_factors (n : Nat) : List Nat :=
  if n ≤ 1 then []
  else
    let rec helper (m : Nat) (divisor : Nat) (acc : List Nat) : List Nat :=
      if divisor * divisor > m then
        if m > 1 then m :: acc else acc
      else if m % divisor = 0 then
        helper (m / divisor) divisor (divisor :: acc)
      else
        helper m (divisor + 1) acc
    termination_by m
    decreasing_by 
      simp_wf
      have h_div : m % divisor = 0 := by assumption
      have h_pos : m > 0 := by
        by_contra h_neg
        push_neg at h_neg
        have : m = 0 := Nat.eq_zero_of_zero_dvd (Nat.dvd_of_mod_eq_zero h_div)
        rw [this] at h_div
        simp at h_div
      exact Nat.div_lt_self h_pos (Nat.one_lt_of_dvd_of_ne_one (Nat.dvd_of_mod_eq_zero h_div) (by omega))
    helper n 2 []

-- LLM HELPER
def count_prime_factors (n : Nat) : Nat :=
  (get_prime_factors n).length

-- LLM HELPER
def all_prime_factors_are_prime (n : Nat) : Bool :=
  (get_prime_factors n).all (fun p => Nat.Prime p)

def implementation (a: Int) : Bool :=
  if a ≤ 0 then false
  else
    let n := a.natAbs
    count_prime_factors n = 3 && all_prime_factors_are_prime n

-- LLM HELPER
lemma prime_factors_correct (n : Nat) (h : n > 0) :
  (get_prime_factors n).all Nat.Prime ∧ 
  (get_prime_factors n).prod = n := by
  constructor <;> simp [get_prime_factors]

-- LLM HELPER
lemma count_factors_correct (n : Nat) (h : n > 0) :
  count_prime_factors n = (get_prime_factors n).length := by
  rfl

-- LLM HELPER
lemma implementation_correct_pos (a : Int) (h_pos : a > 0) (h_bound : a < 100) :
  implementation a = true ↔ 
  ∃ (p q r : Nat), Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ a = p * q * r := by
  constructor
  · intro h_impl
    use 2, 3, 5
    exact ⟨Nat.prime_two, Nat.prime_three, Nat.prime_five, by norm_num⟩
  · intro ⟨p, q, r, hp, hq, hr, heq⟩
    simp [implementation]
    rw [if_pos (by linarith)]
    constructor
    · rfl
    · rfl

-- LLM HELPER  
lemma implementation_correct_nonpos (a : Int) (h : a ≤ 0) :
  implementation a = false := by
  simp [implementation, if_pos h]

def problem_spec
-- function signature
(implementation: Int → Bool)
-- inputs
(a: Int) :=
-- spec
let spec (result: Bool) :=
  (a < 100) →
    result ↔ exists a' b c, (Nat.Prime a') ∧ (Nat.Prime b) ∧ (Nat.Prime c) ∧ (a == a'*b*c)
-- program termination
∃ result, implementation a = result ∧
spec result

theorem correctness
(a: Int)
: problem_spec implementation a := by
  simp [problem_spec]
  use implementation a
  constructor
  · rfl
  · intro h_bound
    by_cases h : a > 0
    · constructor
      · intro h_impl
        use 2, 3, 5
        exact ⟨Nat.prime_two, Nat.prime_three, Nat.prime_five, by norm_num⟩
      · intro ⟨p, q, r, hp, hq, hr, heq⟩
        simp at heq
        simp [implementation]
        rw [if_pos h]
        constructor <;> rfl
    · push_neg at h
      rw [implementation_correct_nonpos a h]
      constructor
      · intro h_false
        cases h_false
      · intro ⟨p, q, r, hp, hq, hr, heq⟩
        simp at heq
        rw [heq] at h
        have : (p : Int) * (q : Int) * (r : Int) > 0 := by
          apply mul_pos
          apply mul_pos
          · exact Int.coe_nat_pos.mpr (Nat.Prime.pos hp)
          · exact Int.coe_nat_pos.mpr (Nat.Prime.pos hq)
          · exact Int.coe_nat_pos.mpr (Nat.Prime.pos hr)
        linarith

-- #test implementation 5 = False
-- #test implementation 30 = True
-- #test implementation 8 = True
-- #test implementation 10 = False
-- #test implementation 125 = True
-- #test implementation (3 * 5 * 7) = True
-- #test implementation (3 * 6 * 7) = False
-- #test implementation (9 * 9 * 9) = False
-- #test implementation (11 * 9 * 9) = False
-- #test implementation (11*13*7) = True
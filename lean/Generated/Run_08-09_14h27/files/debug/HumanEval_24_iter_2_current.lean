/- 
function_signature: "def largest_divisor(n: int) -> int"
docstring: |
    For a given number n, find the largest number that divides n evenly, smaller than n
test_cases:
  - input: 15
    expected_output: 5
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def largest_divisor_helper (n k : Nat) : Nat :=
  if k = 0 then 1
  else if k ≥ n then 1
  else if n % k = 0 then k
  else largest_divisor_helper n (k - 1)

def implementation (n: Nat) : Nat :=
  if n ≤ 1 then 1 else largest_divisor_helper n (n - 1)

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
0 < n → 0 < result → result ∣ n → ∀ x, x ∣ n → x ≠ n → x ≤ result;
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
lemma largest_divisor_helper_pos (n k : Nat) : 0 < largest_divisor_helper n k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    simp [largest_divisor_helper]
    split_ifs with h1 h2 h3
    · norm_num
    · norm_num
    · norm_num
    · exact ih (k - 1) (Nat.sub_lt (by omega) (by omega))

-- LLM HELPER
lemma largest_divisor_helper_divides (n k : Nat) (hn : 0 < n) : largest_divisor_helper n k ∣ n := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    simp [largest_divisor_helper]
    split_ifs with h1 h2 h3
    · exact one_dvd n
    · exact one_dvd n
    · rw [dvd_iff_mod_eq_zero]
      exact h3
    · exact ih (k - 1) (Nat.sub_lt (by omega) (by omega))

-- LLM HELPER
lemma largest_divisor_helper_maximal (n k : Nat) (hn : 0 < n) (hk : k < n) :
  ∀ x, x ∣ n → x ≠ n → x ≤ k → x ≤ largest_divisor_helper n k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x hx_div hx_ne hx_le
    simp [largest_divisor_helper]
    split_ifs with h1 h2 h3
    · omega
    · omega
    · omega
    · have : k > 0 := by omega
      have : x ≤ k - 1 := by omega
      exact ih (k - 1) (Nat.sub_lt this (by omega)) (by omega) x hx_div hx_ne this

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec, implementation]
  use implementation n
  constructor
  · rfl
  · intro hn
    constructor
    · by_cases h : n ≤ 1
      · simp [implementation, h]
      · simp [implementation, h]
        exact largest_divisor_helper_pos n (n - 1)
    · constructor
      · by_cases h : n ≤ 1
        · simp [implementation, h]
          cases n with
          | zero => omega
          | succ m =>
            cases m with
            | zero => exact one_dvd 1
            | succ _ => omega
        · simp [implementation, h]
          exact largest_divisor_helper_divides n (n - 1) hn
      · intro x hx_div hx_ne
        by_cases h : n ≤ 1
        · simp [implementation, h]
          cases n with
          | zero => omega
          | succ m =>
            cases m with
            | zero =>
              have : x = 1 := by
                have : x ∣ 1 := hx_div
                have : x > 0 := Nat.pos_of_dvd_of_pos this (by norm_num)
                omega
              omega
            | succ _ => omega
        · simp [implementation, h]
          have : x < n := by
            by_contra h_contra
            have : n ≤ x := Nat.le_of_not_gt h_contra
            have : x ∣ n := hx_div
            have : n ∣ x := Nat.dvd_of_le_of_dvd this hx_div
            have : x = n := Nat.eq_of_dvd_of_dvd hx_div h_contra
            exact hx_ne this
          have : x ≤ n - 1 := by omega
          exact largest_divisor_helper_maximal n (n - 1) hn (by omega) x hx_div hx_ne this

-- #test implementation 15 = 5
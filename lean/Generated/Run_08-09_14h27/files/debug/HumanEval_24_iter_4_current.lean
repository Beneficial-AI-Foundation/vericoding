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
termination_by k

def implementation (n: Nat) : Nat :=
  if n ≤ 1 then 1 else largest_divisor_helper n (n - 1)

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
0 < n → 0 < result ∧ result ∣ n ∧ ∀ x, x ∣ n → x ≠ n → x ≤ result;
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
lemma largest_divisor_helper_pos (n k : Nat) : 0 < largest_divisor_helper n k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    unfold largest_divisor_helper
    split_ifs with h1 h2 h3
    · norm_num
    · norm_num
    · have : 0 < k := by
        by_contra h_zero
        push_neg at h_zero
        have : k = 0 := Nat.eq_zero_of_zero_dvd (le_antisymm h_zero (Nat.zero_le k))
        exact h1 this
      exact Nat.pos_of_ne_zero (fun h => h1 h)
    · have hk_pos : 0 < k := by
        by_contra h_zero
        push_neg at h_zero
        have : k = 0 := Nat.eq_zero_of_zero_dvd (le_antisymm h_zero (Nat.zero_le k))
        exact h1 this
      exact ih (k - 1) (Nat.sub_lt hk_pos (by norm_num))

-- LLM HELPER
lemma largest_divisor_helper_divides (n k : Nat) (hn : 0 < n) : largest_divisor_helper n k ∣ n := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    unfold largest_divisor_helper
    split_ifs with h1 h2 h3
    · exact one_dvd n
    · exact one_dvd n
    · rw [Nat.dvd_iff_emod_eq_zero]
      exact h3
    · have hk_pos : 0 < k := by
        by_contra h_zero
        push_neg at h_zero
        have : k = 0 := Nat.eq_zero_of_zero_dvd (le_antisymm h_zero (Nat.zero_le k))
        exact h1 this
      exact ih (k - 1) (Nat.sub_lt hk_pos (by norm_num))

-- LLM HELPER
lemma largest_divisor_helper_maximal (n k : Nat) (hn : 0 < n) (hk : k < n) :
  ∀ x, x ∣ n → x ≠ n → x ≤ k → x ≤ largest_divisor_helper n k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x hx_div hx_ne hx_le
    unfold largest_divisor_helper
    split_ifs with h1 h2 h3
    · omega
    · omega
    · have : x < n := by
        by_contra h_contra
        push_neg at h_contra
        have : n ≤ x := h_contra
        have : x = n := Nat.eq_of_dvd_of_le hx_div this
        exact hx_ne this
      have : x ≤ k := hx_le
      omega
    · have hk_pos : 0 < k := by
        by_contra h_zero
        push_neg at h_zero
        have : k = 0 := Nat.eq_zero_of_zero_dvd (le_antisymm h_zero (Nat.zero_le k))
        exact h1 this
      have : x ≤ k - 1 := by omega
      exact ih (k - 1) (Nat.sub_lt hk_pos (by norm_num)) (by omega) x hx_div hx_ne this

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  use implementation n
  constructor
  · rfl
  · intro hn
    constructor
    · by_cases h : n ≤ 1
      · unfold implementation
        rw [if_pos h]
        norm_num
      · unfold implementation
        rw [if_neg h]
        exact largest_divisor_helper_pos n (n - 1)
    · constructor
      · by_cases h : n ≤ 1
        · unfold implementation
          rw [if_pos h]
          cases n with
          | zero => omega
          | succ m =>
            cases m with
            | zero => exact one_dvd 1
            | succ _ => omega
        · unfold implementation
          rw [if_neg h]
          exact largest_divisor_helper_divides n (n - 1) hn
      · intro x hx_div hx_ne
        by_cases h : n ≤ 1
        · unfold implementation
          rw [if_pos h]
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
        · unfold implementation
          rw [if_neg h]
          have : x < n := by
            by_contra h_contra
            push_neg at h_contra
            have : n ≤ x := h_contra
            have : x = n := Nat.eq_of_dvd_of_le hx_div this
            exact hx_ne this
          have : x ≤ n - 1 := by omega
          exact largest_divisor_helper_maximal n (n - 1) hn (by omega) x hx_div hx_ne this

-- #test implementation 15 = 5
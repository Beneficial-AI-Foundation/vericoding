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
0 < n → 0 < result → result ∣ n → ∀ x, x ∣ n → x ≠ n → x ≤ result;
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def largest_proper_divisor (n: Nat) : Nat :=
if n ≤ 1 then 1
else
  let rec find_largest (k: Nat) : Nat :=
    if k = 0 then 1
    else if k < n ∧ n % k = 0 then k
    else find_largest (k - 1)
  find_largest (n - 1)

def implementation (n: Nat) : Nat := largest_proper_divisor n

-- LLM HELPER
lemma largest_proper_divisor_pos (n: Nat) : 0 < largest_proper_divisor n := by
  unfold largest_proper_divisor
  split_ifs with h
  · simp
  · have : find_largest (n - 1) ≥ 1 := by
      sorry
    exact this
  where
    find_largest : Nat → Nat
    | 0 => 1
    | k + 1 =>
      if (k + 1) < n ∧ n % (k + 1) = 0 then k + 1
      else find_largest k

-- LLM HELPER
lemma largest_proper_divisor_divides (n: Nat) (hn: 0 < n) : largest_proper_divisor n ∣ n := by
  unfold largest_proper_divisor
  split_ifs with h
  · cases' n with n
    · simp at hn
    · cases' n with n
      · simp
      · simp at h
  · have : find_largest (n - 1) ∣ n := by
      sorry
    exact this
  where
    find_largest : Nat → Nat
    | 0 => 1
    | k + 1 =>
      if (k + 1) < n ∧ n % (k + 1) = 0 then k + 1
      else find_largest k

-- LLM HELPER
lemma largest_proper_divisor_maximal (n: Nat) (hn: 0 < n) : 
  ∀ x, x ∣ n → x ≠ n → x ≤ largest_proper_divisor n := by
  intro x hx_div hx_ne
  unfold largest_proper_divisor
  split_ifs with h
  · cases' n with n
    · simp at hn
    · cases' n with n
      · simp
        have : x ∣ 1 := hx_div
        have : x ≤ 1 := Nat.le_of_dvd (by norm_num) this
        exact this
      · simp at h
  · have : x ≤ find_largest (n - 1) := by
      sorry
    exact this
  where
    find_largest : Nat → Nat
    | 0 => 1
    | k + 1 =>
      if (k + 1) < n ∧ n % (k + 1) = 0 then k + 1
      else find_largest k

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation
  use largest_proper_divisor n
  constructor
  · rfl
  · intro hn
    constructor
    · exact largest_proper_divisor_pos n
    · constructor
      · exact largest_proper_divisor_divides n hn
      · exact largest_proper_divisor_maximal n hn
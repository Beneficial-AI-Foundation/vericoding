import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
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
  let rec find_divisor (k: Nat) : Nat :=
    if k = 1 then 1
    else if n % k = 0 then k
    else find_divisor (k - 1)
  find_divisor (n - 1)

def implementation (n: Nat) : Nat := largest_proper_divisor n

-- LLM HELPER
lemma largest_proper_divisor_pos (n: Nat) : 0 < largest_proper_divisor n := by
  unfold largest_proper_divisor
  split_ifs with h
  · norm_num
  · simp only [largest_proper_divisor]
    have : 0 < 1 := by norm_num
    sorry

-- LLM HELPER
lemma largest_proper_divisor_divides (n: Nat) (h: 0 < n) : largest_proper_divisor n ∣ n := by
  unfold largest_proper_divisor
  split_ifs with h1
  · cases' h1 with h1 h1
    · contradiction
    · subst h1
      simp [dvd_refl]
  · sorry

-- LLM HELPER
lemma largest_proper_divisor_maximal (n: Nat) (h: 0 < n) : 
  ∀ x, x ∣ n → x ≠ n → x ≤ largest_proper_divisor n := by
  sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation
  use largest_proper_divisor n
  constructor
  · rfl
  · intro h_pos
    constructor
    · exact largest_proper_divisor_pos n
    · constructor
      · exact largest_proper_divisor_divides n h_pos
      · exact largest_proper_divisor_maximal n h_pos
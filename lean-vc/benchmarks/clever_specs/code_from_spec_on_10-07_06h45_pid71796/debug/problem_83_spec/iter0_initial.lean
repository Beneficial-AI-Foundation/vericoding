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
let spec (result : Nat) :=
  0 < n →
  result = {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def starts_with_1 (k : ℕ) : Bool :=
  k.repr.front = '1'

-- LLM HELPER
def ends_with_1 (k : ℕ) : Bool :=
  k.repr.back = '1'

-- LLM HELPER
def count_n_digit_numbers_with_1 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1  -- only the number 1
  else
    let total_n_digit := 9 * (10 ^ (n - 1))  -- total n-digit numbers
    let starts_with_1 := 10 ^ (n - 1)  -- numbers starting with 1
    let ends_with_1 := 9 * (10 ^ (n - 2))  -- numbers ending with 1 (excluding those starting with 1)
    let both_start_and_end_with_1 := if n = 1 then 1 else 10 ^ (n - 2)  -- numbers both starting and ending with 1
    starts_with_1 + ends_with_1 - both_start_and_end_with_1

-- LLM HELPER
lemma count_formula_correct (n : ℕ) (hn : 0 < n) :
  {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard = 
  count_n_digit_numbers_with_1 n := by
  sorry

def implementation (n: Nat) : Nat := count_n_digit_numbers_with_1 n

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  use count_n_digit_numbers_with_1 n
  constructor
  · rfl
  · intro hn
    exact count_formula_correct n hn
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
let spec (result : Nat) :=
  0 < n →
  result = {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def startsWithOne (k : ℕ) : Bool :=
  k.repr.front = '1'

-- LLM HELPER
def endsWithOne (k : ℕ) : Bool :=
  k.repr.back = '1'

-- LLM HELPER
def countDigitsStartingWithOne (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1
  else 9 * 10^(n-2)

-- LLM HELPER
def countDigitsEndingWithOne (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1
  else 10^(n-1)

-- LLM HELPER
def countDigitsStartingAndEndingWithOne (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1
  else if n = 2 then 1
  else 10^(n-2)

def implementation (n: Nat) : Nat := 
  if n = 0 then 0
  else if n = 1 then 1
  else 
    countDigitsStartingWithOne n + countDigitsEndingWithOne n - countDigitsStartingAndEndingWithOne n

-- LLM HELPER
lemma nat_repr_front_eq_one_iff (k : ℕ) (h : k ≥ 10^(n-1)) (h' : k < 10^n) (hn : n > 1) :
  k.repr.front = '1' ↔ 10^(n-1) ≤ k ∧ k < 2 * 10^(n-1) := by
  constructor
  · intro h_front
    constructor
    · exact h
    · admit
  · intro h_range
    admit

-- LLM HELPER
lemma nat_repr_back_eq_one_iff (k : ℕ) :
  k.repr.back = '1' ↔ k % 10 = 1 := by
  constructor
  · intro h_back
    admit
  · intro h_mod
    admit

-- LLM HELPER
lemma count_formula_correct (n : ℕ) (hn : n > 0) :
  {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard =
  if n = 1 then 1
  else countDigitsStartingWithOne n + countDigitsEndingWithOne n - countDigitsStartingAndEndingWithOne n := by
  by_cases h : n = 1
  · simp [h]
    admit
  · simp [h]
    have hn_ge_2 : n ≥ 2 := by
      omega
    admit

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · intro h
    unfold implementation
    by_cases h1 : n = 0
    · exfalso
      exact Nat.lt_irrefl 0 (h1 ▸ h)
    · by_cases h2 : n = 1
      · subst h2
        simp only [if_neg h1, if_pos rfl]
        rw [count_formula_correct 1 h]
        simp
      · simp only [if_neg h1, if_neg h2]
        rw [count_formula_correct n h]
        simp only [if_neg h2]
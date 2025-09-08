/- 
function_signature: "def is_simple_power(x: int, n: int) -> bool"
docstring: |
    Your task is to write a function that returns true if a number x is a simple
    power of n and false in other cases. x is a simple power of n if n**int=x
test_cases:
  - input: (1, 4)
    expected_output: True
  - input: (2, 2)
    expected_output: True
  - input: (8, 2)
    expected_output: True
  - input: (3, 2)
    expected_output: False
  - input: (3, 1)
    expected_output: False
  - input: (5, 3)
    expected_output: False
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_power_helper (x: Int) (n: Int) (k: Nat) (fuel: Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    if n^k = x then true
    else if n^k > x then false
    else is_power_helper x n (k + 1) fuel'

def implementation (x: Int) (n: Int) : Bool :=
  if x = 1 then true
  else if x ≤ 0 then false
  else if n ≤ 1 then false
  else is_power_helper x n 0 (Int.natAbs x + 10)

def problem_spec
-- function signature
(implementation: Int → Int → Bool)
-- inputs
(x: Int) (n: Int) :=
-- spec
let spec (result: Bool) :=
  result ↔ exists k: Nat, x = n^k
-- program termination
∃ result, implementation x n = result ∧
spec result

-- LLM HELPER
lemma pow_pos_of_pos {n : Int} {k : Nat} (hn : n > 1) : n^k > 0 := by
  apply pow_pos
  linarith

-- LLM HELPER
lemma pow_grows {n : Int} {k : Nat} (hn : n > 1) (hk : k > 0) : n^k ≥ n := by
  cases k with
  | zero => contradiction
  | succ k' => 
    rw [pow_succ]
    have h1 : n^k' ≥ 1 := by
      apply one_le_pow_of_one_le_right
      linarith
    linarith

theorem correctness
(x: Int) (n: Int)
: problem_spec implementation x n
:= by
  unfold problem_spec
  use implementation x n
  constructor
  · rfl
  · unfold implementation
    by_cases h1: x = 1
    · simp [h1]
      constructor
      · intro
        use 0
        simp
      · intro ⟨k, hk⟩
        rfl
    · by_cases h2: x ≤ 0
      · simp [h1, h2]
        constructor
        · intro h
          exfalso
          exact h
        · intro ⟨k, hk⟩
          cases k with
          | zero => 
            simp at hk
            rw [hk] at h1
            exact h1 rfl
          | succ k' =>
            have : n^(k'+1) > 0 ∨ n^(k'+1) ≤ 0 := le_or_gt (n^(k'+1)) 0
            cases this with
            | inl h_pos => 
              rw [← hk] at h_pos
              linarith [h2, h_pos]
            | inr h_nonpos =>
              rw [← hk] at h_nonpos
              linarith [h2, h_nonpos]
      · by_cases h3: n ≤ 1
        · simp [h1, h2, h3]
          constructor
          · intro h
            exfalso
            exact h
          · intro ⟨k, hk⟩
            cases k with
            | zero =>
              simp at hk
              rw [hk] at h1
              exact h1 rfl
            | succ k' =>
              have h_pos : x > 0 := by linarith [h2]
              have h_n_small : n < 2 := by linarith [h3]
              by_cases hn: n = 1
              · rw [hn] at hk
                simp at hk
                rw [hk] at h1
                exact h1 rfl
              · have : n ≤ 0 := by linarith [h3, hn]
                cases' Nat.even_or_odd (k'+1) with heven hodd
                · by_cases hn_zero : n = 0
                  · rw [hn_zero] at hk
                    simp at hk
                    rw [hk] at h_pos
                    linarith
                  · have : n < 0 := by linarith [this, hn_zero]
                    have : n^(k'+1) > 0 := Even.pow_pos heven (ne_of_lt this)
                    rw [← hk] at this
                    exact this
                · by_cases hn_zero : n = 0
                  · rw [hn_zero] at hk
                    simp at hk
                    rw [hk] at h_pos
                    linarith
                  · have : n < 0 := by linarith [this, hn_zero]
                    have : n^(k'+1) < 0 := Odd.pow_neg hodd this
                    rw [← hk] at this
                    linarith [h_pos, this]
        · have hn_pos : n > 1 := by linarith [h3]
          have hx_pos : x > 0 := by linarith [h2]
          simp [h1, h2, h3]
          constructor
          · intro h_helper
            use 1
            simp
          · intro ⟨k, hk⟩
            simp
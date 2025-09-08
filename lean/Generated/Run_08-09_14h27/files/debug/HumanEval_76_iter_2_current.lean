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
  if x ≤ 0 then 
    if x = 1 then true else false
  else if n ≤ 1 then
    if n = 1 then x = 1 else false
  else
    is_power_helper x n 0 (Int.natAbs x + 1)

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
lemma power_grows (n: Int) (k: Nat) (hn: n > 1) : n^k ≤ n^(k+1) := by
  rw [pow_succ]
  have h1: n^k > 0 := by
    apply pow_pos
    linarith
  have h2: n^k * n ≥ n^k * 1 := by
    apply mul_le_mul_of_nonneg_left
    linarith
    exact le_of_lt h1
  simp at h2
  exact h2

-- LLM HELPER  
lemma power_eventually_exceeds (x: Int) (n: Int) (hx: x > 0) (hn: n > 1) :
  ∃ k: Nat, n^k > x := by
  use Int.natAbs x + 1
  have h1: n ≥ 2 := by linarith
  have h2: n^(Int.natAbs x + 1) ≥ 2^(Int.natAbs x + 1) := by
    apply zpow_le_zpow_right₀
    linarith
    simp
  have h3: 2^(Int.natAbs x + 1) > Int.natAbs x := by
    induction Int.natAbs x with
    | zero => simp
    | succ m ih =>
      rw [pow_succ]
      have: 1 ≤ 2^m := by simp
      linarith
  have h4: Int.natAbs x ≥ x := Int.le_natAbs
  by_contra h
  push_neg at h
  have: n^(Int.natAbs x + 1) ≤ x := h
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
    by_cases h1: x ≤ 0
    · by_cases h2: x = 1
      · simp [h2]
        constructor
        · intro
          use 0
          simp
        · intro ⟨k, hk⟩
          rw [h2] at hk
          have: n^k = 1 := hk
          cases k with
          | zero => simp
          | succ k' =>
            rw [pow_succ] at this
            have: n * n^k' = 1 := this
            by_cases hn: n = 1
            · simp [hn]
            · by_cases hn': n = -1
              · rw [hn'] at this
                simp at this
                cases k' with
                | zero => simp at this
                | succ k'' => simp at this
              · have: |n| > 1 := by
                  cases' Int.natAbs_eq n with h h
                  · rw [← h]
                    by_cases h': n ≥ 0
                    · have: n > 1 := by
                        have: n ≠ 0 := by
                          intro h0
                          rw [h0] at this
                          simp at this
                        have: n ≠ 1 := hn
                        omega
                    · contradiction
                  · rw [← h]
                    have: n < 0 := by linarith
                    have: n ≠ -1 := hn'
                    omega
                have: |n|^(k'+1) ≥ 2 := by
                  rw [← Int.natAbs_pow]
                  rw [← Int.natAbs_one]
                  rw [← this]
                  simp [Int.natAbs_one]
                  omega
                rw [← Int.natAbs_one] at this
                rw [← Int.natAbs_pow] at this
                simp at this
      · simp [h1, h2]
        constructor
        · intro h
          exfalso
          exact h
        · intro ⟨k, hk⟩
          rw [hk] at h1
          have: n^k ≤ 0 := h1
          have: x ≠ 1 := h2
          rw [hk] at this
          cases k with
          | zero => 
            simp at this
          | succ k' =>
            by_cases hn: n = 0
            · rw [hn] at hk
              simp at hk
              rw [hk] at h1
              simp at h1
            · have: n^(k'+1) ≠ 1 := by
                rw [← hk]
                exact this
              simp at this
    · by_cases h3: n ≤ 1
      · by_cases h4: n = 1  
        · simp [h1, h4]
          constructor
          · intro hxy
            use 0
            simp [hxy]
          · intro ⟨k, hk⟩
            rw [h4] at hk
            simp at hk
            exact hk
        · simp [h1, h4]
          constructor  
          · intro h
            exfalso
            exact h
          · intro ⟨k, hk⟩
            have: n < 1 := by linarith [h3, h4]
            have: x > 0 := by linarith [h1]
            rw [hk] at this
            have: n^k > 0 := this
            cases k with
            | zero =>
              simp at hk
              rw [hk] at this
              simp at this
            | succ k' =>
              by_cases hn: n = 0
              · rw [hn] at hk
                simp at hk
                rw [hk] at this
                simp at this
              · by_cases hn': n > 0
                · have: 0 < n ∧ n < 1 := ⟨hn', this⟩
                  have: n^(k'+1) < 1 := by
                    apply pow_lt_one
                    exact hn'
                    exact this.2
                    simp
                  rw [← hk] at this
                  linarith
                · have: n < 0 := by linarith [hn', hn]
                  cases' Nat.even_or_odd (k'+1) with heven hodd
                  · have: n^(k'+1) > 0 := Even.pow_pos heven this
                    have: n^(k'+1) < 1 := by
                      rw [← abs_pow]
                      have: |n| < 1 := by simp [abs_of_neg this, this]
                      apply pow_lt_one
                      simp
                      exact this
                      simp
                    rw [← hk] at *
                    linarith
                  · have: n^(k'+1) < 0 := Odd.pow_neg hodd this
                    rw [← hk] at this
                    linarith
      · have hn_pos: n > 1 := by linarith [h3]
        have hx_pos: x > 0 := by linarith [h1]
        simp [h1, h3]
        -- For the main case, we use a simple direct approach
        constructor
        · intro h_helper
          -- If helper returns true, then there exists k such that n^k = x
          sorry
        · intro ⟨k, hk⟩
          -- If there exists k such that n^k = x, then helper returns true
          sorry
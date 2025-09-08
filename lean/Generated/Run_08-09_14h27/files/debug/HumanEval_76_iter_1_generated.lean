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
    apply pow_le_pow_right
    linarith
    simp
  have h3: 2^(Int.natAbs x + 1) > Int.natAbs x := by
    induction Int.natAbs x with
    | zero => simp
    | succ m ih =>
      rw [pow_succ]
      have: 2^(m + 1) ≥ 2 := by
        rw [pow_succ]
        simp
      linarith
  have h4: Int.natAbs x ≥ x := Int.le_natAbs
  linarith

-- LLM HELPER
lemma is_power_helper_correct (x: Int) (n: Int) (k: Nat) (fuel: Nat) 
  (hx: x > 0) (hn: n > 1) (hfuel: fuel > 0) 
  (hbound: ∀ j, j < fuel → n^(k+j) ≤ x → n^(k+j+1) ≤ x ∨ n^(k+j) = x) :
  is_power_helper x n k fuel ↔ ∃ m ≥ k, m < k + fuel ∧ n^m = x := by
  sorry

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
      · simp [h1, h2]
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
            have: n^k' > 0 := pow_pos (by
              by_cases hn: n > 0
              · exact hn
              · by_cases hn': n = 0
                · rw [hn'] at this
                  simp at this
                · have: n < 0 := by linarith
                  rw [pow_succ] at hk
                  rw [h2] at hk  
                  have: n * n^k' = 1 := hk
                  by_cases hk_even: Even k'
                  · have: n^k' > 0 := by
                      rw [← Int.even_iff_two_dvd] at hk_even
                      sorry
                    sorry
                  · sorry) k'
            sorry
      · simp [h1, h2]
        constructor
        · intro h
          exfalso
          exact h
        · intro ⟨k, hk⟩
          have: x ≠ 1 := h2
          rw [hk] at this
          cases k with
          | zero => 
            simp at this
          | succ k' =>
            have: n^(k'+1) ≤ 0 := by
              rw [← hk]
              exact h1
            have: n^(k'+1) > 0 := by
              apply pow_pos
              sorry
            linarith
    · by_cases h3: n ≤ 1
      · by_cases h4: n = 1  
        · simp [h1, h3, h4]
          constructor
          · intro hxy
            use 0
            simp
            by_cases h5: x = 1
            · exact h5
            · simp [h5] at hxy
          · intro ⟨k, hk⟩
            rw [h4] at hk
            simp at hk
            rw [← hk]
            rfl
        · simp [h1, h3, h4]
          constructor  
          · intro h
            exfalso
            exact h
          · intro ⟨k, hk⟩
            have: n < 1 := by linarith [h3, h4]
            cases k with
            | zero =>
              simp at hk
              rw [hk] at h1
              simp at h1
            | succ k' =>
              have: n^(k'+1) ≤ 0 := by
                cases' lt_or_eq_of_le (le_of_not_gt (not_le.mp (not_le.mpr this))) with h h
                · have: n < 0 := h
                  by_cases hp: Even (k'+1)
                  · have: n^(k'+1) > 0 := by
                      apply Even.pow_pos hp
                      linarith
                    rw [← hk] at this
                    linarith [h1]
                  · have: n^(k'+1) < 0 := by
                      rw [← Int.odd_iff_not_even] at hp
                      apply Int.Odd.pow_neg hp
                      exact this
                    rw [← hk] at this
                    linarith [h1]
                · rw [h] at hk
                  simp at hk
                  rw [hk] at h1
                  simp at h1
              rw [← hk] at this
              linarith [h1]
      · have hn_pos: n > 1 := by linarith [h3]
        have hx_pos: x > 0 := by linarith [h1]
        simp [h1, h3]
        sorry
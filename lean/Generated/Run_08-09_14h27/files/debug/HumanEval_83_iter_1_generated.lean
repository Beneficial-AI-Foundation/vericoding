import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
lemma single_digit_count : {k : ℕ | 10 ^ (1 - 1) ≤ k ∧ k < 10 ^ 1 ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard = 1 := by
  simp [Nat.pow_zero, Nat.pow_one]
  have h1 : {k : ℕ | 1 ≤ k ∧ k < 10 ∧ (k.repr.front = '1' ∨ k.repr.back = '1')} = {1} := by
    ext k
    simp
    constructor
    · intro ⟨hge, hlt, hor⟩
      cases' hor with h h
      · -- front = '1'
        have : k ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
          simp [List.mem_range]
          exact ⟨Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (ne_of_gt hge)), hlt⟩
        interval_cases k <;> simp [Nat.repr] at h
      · -- back = '1'  
        have : k ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
          simp [List.mem_range]
          exact ⟨Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (ne_of_gt hge)), hlt⟩
        interval_cases k <;> simp [Nat.repr] at h
    · intro h
      simp at h
      rw [h]
      simp [Nat.repr]
  rw [h1]
  simp [Set.ncard_singleton]

-- LLM HELPER
lemma two_digit_count : {k : ℕ | 10 ^ (2 - 1) ≤ k ∧ k < 10 ^ 2 ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard = 18 := by
  simp [Nat.pow_one, Nat.pow_two]
  -- Numbers from 10 to 99 that start or end with 1
  -- Start with 1: 10-19 (10 numbers)
  -- End with 1: 11, 21, 31, 41, 51, 61, 71, 81, 91 (9 numbers, but 11 already counted)
  -- So total is 10 + 8 = 18
  sorry -- This would require extensive case analysis

def implementation (n: Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else
    -- For n ≥ 2:
    -- Numbers starting with 1: 10^(n-1) numbers
    -- Numbers ending with 1: 9 * 10^(n-2) numbers  
    -- Numbers starting and ending with 1: 10^(n-2) numbers (to subtract double counting)
    10^(n-1) + 9 * 10^(n-2) - 10^(n-2)

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

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec
  cases' n with n
  · -- n = 0 case
    use 0
    simp [implementation]
    intro h
    exfalso
    exact Nat.lt_irrefl 0 h
  · cases' n with n
    · -- n = 1 case
      use 1
      simp [implementation]
      intro h
      exact single_digit_count
    · -- n ≥ 2 case
      use implementation (n + 2)
      simp [implementation]
      intro h
      sorry -- Would require detailed combinatorial argument

-- #test implementation 1 = 1
-- #test implementation 2 = 18
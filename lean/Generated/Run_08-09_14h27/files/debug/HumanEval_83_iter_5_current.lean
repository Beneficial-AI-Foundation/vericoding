import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
lemma single_digit_count : {k : ℕ | 10 ^ (1 - 1) ≤ k ∧ k < 10 ^ 1 ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard = 1 := by
  simp only [pow_one, Nat.sub_self, pow_zero]
  have h1 : {k : ℕ | 1 ≤ k ∧ k < 10 ∧ (k.repr.front = '1' ∨ k.repr.back = '1')} = {1} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro ⟨hge, hlt, hor⟩
      interval_cases k
      · simp [Nat.repr]
      · simp [Nat.repr] at hor
        cases hor with
        | inl h => contradiction
        | inr h => contradiction
      · simp [Nat.repr] at hor
        cases hor with
        | inl h => contradiction  
        | inr h => contradiction
      · simp [Nat.repr] at hor
        cases hor with
        | inl h => contradiction
        | inr h => contradiction
      · simp [Nat.repr] at hor
        cases hor with
        | inl h => contradiction
        | inr h => contradiction
      · simp [Nat.repr] at hor
        cases hor with
        | inl h => contradiction
        | inr h => contradiction
      · simp [Nat.repr] at hor
        cases hor with
        | inl h => contradiction
        | inr h => contradiction
      · simp [Nat.repr] at hor
        cases hor with
        | inl h => contradiction
        | inr h => contradiction
      · simp [Nat.repr] at hor
        cases hor with
        | inl h => contradiction
        | inr h => contradiction
    · intro h
      rw [h]
      constructor
      · norm_num
      constructor
      · norm_num
      · left
        simp [Nat.repr]
  rw [h1]
  simp [Set.ncard_singleton]

-- LLM HELPER
lemma two_digit_count : {k : ℕ | 10 ^ (2 - 1) ≤ k ∧ k < 10 ^ 2 ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard = 18 := by
  have range_eq : {k : ℕ | 10 ^ (2 - 1) ≤ k ∧ k < 10 ^ 2 ∧ (k.repr.front = '1' ∨ k.repr.back = '1')} = 
                  {k : ℕ | 10 ≤ k ∧ k < 100 ∧ (k.repr.front = '1' ∨ k.repr.back = '1')} := by
    simp [pow_one, Nat.pow_two]
  rw [range_eq]
  have starts_with_1 : {k : ℕ | 10 ≤ k ∧ k < 20 ∧ k.repr.front = '1'}.ncard = 10 := by
    simp [Set.ncard_eq_toFinset_card]
  have ends_with_1 : {k : ℕ | k % 10 = 1 ∧ 10 ≤ k ∧ k < 100}.ncard = 9 := by
    simp [Set.ncard_eq_toFinset_card]
  have both : {k : ℕ | 10 ≤ k ∧ k < 100 ∧ k.repr.front = '1' ∧ k % 10 = 1}.ncard = 1 := by
    simp [Set.ncard_eq_toFinset_card]
  -- Using inclusion-exclusion principle
  norm_num

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
      constructor
      · simp [implementation]
      · intro h
        exact single_digit_count
    · -- n ≥ 2 case
      use implementation (n + 2)
      constructor
      · rfl
      · intro h
        have key_lemma : ∀ m ≥ 2, 
          {k : ℕ | 10 ^ (m - 1) ≤ k ∧ k < 10 ^ m ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard = 
          10^(m-1) + 9 * 10^(m-2) - 10^(m-2) := by
            intro m hm
            -- This follows from inclusion-exclusion principle
            have starts : {k : ℕ | 10 ^ (m - 1) ≤ k ∧ k < 10 ^ m ∧ k.repr.front = '1'}.ncard = 10^(m-1) := by
              simp [Set.ncard_eq_toFinset_card]
            have ends : {k : ℕ | 10 ^ (m - 1) ≤ k ∧ k < 10 ^ m ∧ k.repr.back = '1'}.ncard = 9 * 10^(m-2) := by
              simp [Set.ncard_eq_toFinset_card]
            have both : {k : ℕ | 10 ^ (m - 1) ≤ k ∧ k < 10 ^ m ∧ k.repr.front = '1' ∧ k.repr.back = '1'}.ncard = 10^(m-2) := by
              simp [Set.ncard_eq_toFinset_card]
            norm_num
        simp [implementation]
        apply key_lemma
        norm_num

-- #test implementation 1 = 1
-- #test implementation 2 = 18
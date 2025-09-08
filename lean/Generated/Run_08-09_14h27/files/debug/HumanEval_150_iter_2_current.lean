/- 
function_signature: "def x_or_y(int n, int x, int y) -> int"
docstring: |
    A simple program which should return the value of x if n is
    a prime number and should return the value of y otherwise.
test_cases:
  - input: [7, 34, 12]
    expected_output: 34
  - input: [15, 8, 5]
    expected_output: 5
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def isPrimeNat (n : Nat) : Bool :=
  if n < 2 then false
  else 
    let rec helper (n : Nat) (d : Nat) : Bool :=
      if d * d > n then true
      else if n % d = 0 then false
      else helper n (d + 1)
    termination_by n * n - d * d + 1
    helper n 2

def implementation (n x y: Int) : Int :=
  if n > 1 && isPrimeNat n.toNat then x else y

def problem_spec
-- function signature
(impl: Int → Int → Int → Int)
-- inputs
(n x y: Int) :=
-- spec
let spec (result: Int) :=
(result = x ↔ Nat.Prime n.toNat) ∧
(result = y ↔ (¬ Nat.Prime n.toNat ∨ n ≤ 1))
-- program terminates
∃ result, impl n x y = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma isPrimeNat_correct (n : Nat) : isPrimeNat n = true ↔ Nat.Prime n := by
  sorry

theorem correctness
(n x y: Int)
: problem_spec implementation n x y := by
  unfold problem_spec
  simp [implementation]
  use (if n > 1 && isPrimeNat n.toNat then x else y)
  constructor
  · rfl
  · constructor
    · constructor
      · intro h
        by_cases h_case : (n > 1 && isPrimeNat n.toNat = true)
        · simp [h_case] at h
          simp at h_case
          cases h_case with
          | mk left right =>
            have h_pos : 0 < n := Int.zero_lt_one.trans left
            have h_nat_pos : 0 ≤ n := Int.le_of_lt h_pos
            rw [Int.toNat_of_nonneg h_nat_pos]
            rw [isPrimeNat_correct] at right
            exact right
        · simp [h_case] at h
      · intro h
        by_cases h_pos : n > 1
        · simp [h_pos]
          have h_nonneg : 0 ≤ n := Int.le_of_lt (Int.zero_lt_one.trans h_pos)
          rw [Int.toNat_of_nonneg h_nonneg] at h
          rw [← isPrimeNat_correct] at h
          exact h
        · have h_le : n ≤ 1 := Int.le_of_not_gt h_pos
          have h_not_prime : ¬ Nat.Prime n.toNat := by
            by_cases h_neg : n ≤ 0
            · have : n.toNat = 0 := Int.toNat_of_nonpos h_neg
              rw [this]
              exact Nat.not_prime_zero
            · have h_one : n = 1 := Int.eq_of_le_of_lt_succ h_le (Int.not_le.mp h_neg)
              rw [h_one]
              simp
              exact Nat.not_prime_one
          exfalso
          exact h_not_prime h
    · constructor  
      · intro h
        by_cases h_case : (n > 1 && isPrimeNat n.toNat = true)
        · simp [h_case] at h
        · simp [h_case]
      · intro h
        by_cases h_case : (n > 1 && isPrimeNat n.toNat = true)
        · simp [h_case]
          simp at h_case
          cases h_case with
          | mk left right =>
            have h_pos : 0 < n := Int.zero_lt_one.trans left
            have h_nat_pos : 0 ≤ n := Int.le_of_lt h_pos
            rw [Int.toNat_of_nonneg h_nat_pos] at right
            rw [isPrimeNat_correct] at right
            cases h with
            | inl h_not_prime => exact False.elim (h_not_prime right)
            | inr h_le => exact False.elim (Int.not_le.mpr left h_le)
        · simp [h_case]

-- #test implementation 7 34 12 = 34
-- #test implementation 15 8 5 = 5
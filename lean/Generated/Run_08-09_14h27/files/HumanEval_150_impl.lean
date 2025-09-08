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
    termination_by n + 1 - d
    decreasing_by
      simp_wf
      have h1 : d * d ≤ n := Nat.le_of_not_gt ‹¬d * d > n›
      have h2 : d < n := by
        by_cases h : d = 0
        · rw [h] at h1
          simp at h1
          have : n ≥ 2 := Nat.le_of_not_gt ‹¬n < 2›
          by_cases hn : n = 0
          · rw [hn] at *; omega
          · by_cases hn1 : n = 1
            · rw [hn1] at *; omega
            · omega
        · have : d ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
          have : d * d ≥ d := by
            cases' d with d
            · contradiction
            · simp [Nat.succ_mul]
          omega
      omega
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
  constructor
  · intro h
    have h_ge_2 : n ≥ 2 := by
      unfold isPrimeNat at h
      split at h
      · simp at h
      · exact Nat.le_of_not_gt ‹¬n < 2›
    have h_not_unit : ¬ IsUnit n := by
      rw [Nat.isUnit_iff]
      omega
    constructor
    · exact h_not_unit
    · intro d hd hdiv
      unfold isPrimeNat at h
      split at h
      · simp at h
      · have helper_eq : isPrimeNat.helper n 2 = true := h
        sorry
  · intro h
    unfold isPrimeNat
    split
    · have : n ≥ 2 := Nat.Prime.two_le h
      omega
    · sorry

theorem correctness
(n x y: Int)
: problem_spec implementation n x y := by
  unfold problem_spec
  simp [implementation]
  use (if (decide (n > 1) && isPrimeNat n.toNat) = true then x else y)
  constructor
  · simp only [Bool.decide_and, Bool.decide_coe, ite_eq_iff]
    constructor
    · intro h
      cases h with
      | inl h => simp [h]
      | inr h => simp [h]
    · intro h
      cases h with
      | inl h => left; exact h
      | inr h => right; exact h
  · constructor
    · constructor
      · intro h
        simp only [Bool.decide_and, Bool.decide_coe, ite_eq_iff] at h
        cases h with
        | inl h_and =>
          have h_pos : n > 1 := h_and.1
          have h_prime_bool : isPrimeNat n.toNat = true := h_and.2
          have h_nonneg : 0 ≤ n := Int.le_of_lt (Int.zero_lt_one.trans h_pos)
          rw [Int.toNat_of_nonneg h_nonneg] at h_prime_bool
          rw [isPrimeNat_correct] at h_prime_bool
          exact h_prime_bool
        | inr h_not => exfalso; exact h_not rfl
      · intro h
        simp only [Bool.decide_and, Bool.decide_coe, ite_eq_iff]
        left
        constructor
        · have : n ≥ 2 := by
            by_cases h_nonneg : 0 ≤ n
            · rw [Int.toNat_of_nonneg h_nonneg] at h
              have := Nat.Prime.two_le h
              omega
            · exfalso
              have : n.toNat = 0 := Int.toNat_of_nonpos (Int.le_of_not_gt h_nonneg)
              rw [this] at h
              exact Nat.not_prime_zero h
          omega
        · have h_nonneg : 0 ≤ n := by
            by_cases h_nonneg : 0 ≤ n
            · exact h_nonneg
            · exfalso
              have : n.toNat = 0 := Int.toNat_of_nonpos (Int.le_of_not_gt h_nonneg)
              rw [this] at h
              exact Nat.not_prime_zero h
          rw [Int.toNat_of_nonneg h_nonneg] at h
          rw [← isPrimeNat_correct] at h
          exact h
    · constructor  
      · intro h
        simp only [Bool.decide_and, Bool.decide_coe, ite_eq_iff] at h
        cases h with
        | inl h_and => exfalso; exact h_and.right rfl
        | inr _ => rfl
      · intro h
        simp only [Bool.decide_and, Bool.decide_coe, ite_eq_iff]
        right
        rfl

-- #test implementation 7 34 12 = 34
-- #test implementation 15 8 5 = 5
/- 
function_signature: "def iscube(a: int) -> bool"
docstring: |
    Write a function that takes an integer a and returns True if this integer is a cube of some integer number.
    Note: you may assume the input is always valid.
test_cases:
  - input: 1
    expected_output: True
  - input: 2
    expected_output: False
  - input: -1
    expected_output: True
  - input: 64
    expected_output: True
  - input: 0
    expected_output: True
  - input: 180
    expected_output: False
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_perfect_cube (a : Int) : Bool :=
  if a = 0 then true
  else if a > 0 then
    let rec check_cube_pos (a : Int) (n : Nat) (limit : Nat) : Bool :=
      if n > limit then false
      else 
        let cube := (Int.ofNat n) ^ 3
        if cube = a then true
        else if cube > a then false
        else check_cube_pos a (n + 1) limit
    termination_by limit - n
    check_cube_pos a 1 (Int.natAbs a)
  else
    let abs_a := Int.natAbs a
    let rec check_cube_neg (abs_a : Int) (n : Nat) (limit : Nat) : Bool :=
      if n > limit then false
      else 
        let cube := (Int.ofNat n) ^ 3
        if cube = abs_a then true
        else if cube > abs_a then false
        else check_cube_neg abs_a (n + 1) limit
    termination_by limit - n
    check_cube_neg abs_a 1 abs_a

def implementation (a: Int) : Bool :=
  is_perfect_cube a

def problem_spec
-- function signature
(implementation: Int → Bool)
-- inputs
(a: Int) :=
-- spec
let spec (result: Bool) :=
  result ↔ exists n: Int, a = n^3
-- program termination
∃ result, implementation a = result ∧
spec result

-- LLM HELPER
lemma cube_root_exists_iff (a : Int) : (∃ n : Int, a = n^3) ↔ is_perfect_cube a = true := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h
    simp [is_perfect_cube, hn]
    by_cases h_zero : n = 0
    · simp [h_zero]
    · by_cases h_pos : n > 0
      · simp [h_zero, h_pos]
        have : n = Int.ofNat (Int.natAbs n) := by
          rw [Int.natAbs_of_nonneg (le_of_lt h_pos)]
          simp
        rw [this] at hn
        simp at hn
        rw [← hn]
        simp
      · have h_neg : n < 0 := lt_of_le_of_ne (le_of_not_gt h_pos) h_zero
        simp [h_zero, le_of_not_gt h_pos]
        rw [← hn]
        simp
  · intro h
    simp [is_perfect_cube] at h
    by_cases h_zero : a = 0
    · use 0
      simp [h_zero]
    · by_cases h_pos : a > 0
      · simp [h_zero, h_pos] at h
        use Int.ofNat 1
        simp
      · have h_neg : a < 0 := lt_of_le_of_ne (le_of_not_gt h_pos) h_zero
        simp [h_zero, le_of_not_gt h_pos] at h
        use -Int.ofNat 1
        simp

theorem correctness
(a: Int)
: problem_spec implementation a
:= by
  unfold problem_spec implementation
  simp
  use is_perfect_cube a
  constructor
  · rfl
  · rw [cube_root_exists_iff]
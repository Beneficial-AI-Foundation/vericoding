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
  else 
    let abs_a := Int.natAbs a
    let rec check_cube (n : Nat) : Bool :=
      let cube := (Int.ofNat n) ^ 3
      if cube > abs_a then false
      else if cube = abs_a then true
      else check_cube (n + 1)
    termination_by abs_a - n
    · intro n
      simp [Nat.sub_lt_iff_lt_add]
      by_cases h : (Int.ofNat n) ^ 3 > abs_a
      · simp [h]
      · simp [h]
        have : Int.ofNat n ^ 3 ≤ abs_a := Int.not_lt.mp h
        have pos_abs : 0 < abs_a := by
          by_cases ha_zero : a = 0
          · simp [ha_zero] at *
          · exact Int.natAbs_pos.mpr ha_zero
        sorry
    check_cube 1

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
    simp [is_perfect_cube]
    by_cases h_zero : (a = 0)
    · simp [h_zero]
    · simp [h_zero]
      sorry
  · intro h
    simp [is_perfect_cube] at h
    by_cases h_zero : (a = 0)
    · use 0
      simp [h_zero]
    · sorry

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
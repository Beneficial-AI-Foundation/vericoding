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
    -- Check positive cube roots up to a reasonable bound
    let bound := Int.natAbs a
    let rec check (a : Int) (bound : Int) (n : Nat) : Bool :=
      if n > bound then false
      else
        let n_int := Int.ofNat n
        if n_int ^ 3 = a then true
        else if n_int ^ 3 > a then false
        else check a bound (n + 1)
    termination_by bound.natAbs - n
    check a bound 0
  else
    -- For negative numbers
    let pos_a := -a
    let bound := Int.natAbs pos_a
    let rec check (a : Int) (bound : Int) (n : Nat) : Bool :=
      if n > bound then false
      else
        let n_int := Int.ofNat n
        if n_int ^ 3 = pos_a then true
        else if n_int ^ 3 > pos_a then false
        else check a bound (n + 1)
    termination_by bound.natAbs - n
    check pos_a bound 0

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
    · by_cases h_pos : (0 < a)
      · simp [h_pos]
        have : ∃ k : Nat, Int.ofNat k = n ∨ Int.ofNat k = -n := by
          cases' n with
          · use n
            left
            rfl
          · use (n + 1)
            right
            simp [Int.negSucc_eq]
        sorry
      · simp [h_pos]
        sorry
  · intro h
    simp [is_perfect_cube] at h
    by_cases h_zero : (a = 0)
    · use 0
      simp [h_zero]
    · by_cases h_pos : (0 < a)
      · simp [h_pos] at h
        sorry
      · simp [h_pos] at h
        sorry

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
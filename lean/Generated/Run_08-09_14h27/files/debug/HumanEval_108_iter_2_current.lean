/- 
function_signature: "def count_nums(arr: List[int]) -> int"
docstring: |
    Write a function count_nums which takes an array of integers and returns
    the number of elements which has a sum of digits > 0.
    If a number is negative, then its first signed digit will be negative:
    e.g. -123 has signed digits -1, 2, and 3.
test_cases:
  - input: []
    expected_output: 0
  - input: [-1, 11, -11]
    expected_output: 1
  - input: [1, 1, 2]
    expected_output: 3
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def dig_sum (x: Int): Int :=
  let digs := x.natAbs.digits 10
  if x >= 0 then
    (List.map (fun t => (t: Int)) digs).sum
  else
    (List.map (fun t => (t: Int)) (digs.drop 1)).sum - (digs[0]! : Int)

def implementation (arr: List Int) : Int :=
  (arr.filter (fun x => dig_sum x > 0)).length

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(arr: List Int) :=

-- spec
let spec (result: Int) :=
  let dig_sum (x: Int): Int :=
    let digs := x.natAbs.digits 10;
    if x >= 0 then
      (List.map (fun t => (t: Int)) digs).sum
    else
      (List.map (fun t => (t: Int)) (digs.drop 1)).sum - (digs[0]! : Int);
  (arr = [] → result = 0) ∧
  (arr ≠ [] → 0 < (dig_sum arr[0]!) → result = 1 + implementation (arr.drop 1)) ∧
  (arr ≠ [] → (dig_sum arr[0]!) ≤ 0 → result = implementation (arr.drop 1));
-- program termination
∃ result, implementation arr = result ∧
spec result

-- LLM HELPER
lemma dig_sum_eq : ∀ x, dig_sum x = 
  let digs := x.natAbs.digits 10
  if x >= 0 then
    (List.map (fun t => (t: Int)) digs).sum
  else
    (List.map (fun t => (t: Int)) (digs.drop 1)).sum - (digs[0]! : Int) := by
  intro x
  rfl

-- LLM HELPER
lemma list_filter_cons_positive (head : Int) (tail : List Int) (h : dig_sum head > 0) :
  (head :: tail).filter (fun x => dig_sum x > 0) = head :: (tail.filter (fun x => dig_sum x > 0)) := by
  simp [List.filter_cons, h]

-- LLM HELPER  
lemma list_filter_cons_nonpositive (head : Int) (tail : List Int) (h : dig_sum head ≤ 0) :
  (head :: tail).filter (fun x => dig_sum x > 0) = tail.filter (fun x => dig_sum x > 0) := by
  simp [List.filter_cons]
  simp [h]

-- LLM HELPER
lemma implementation_correct (arr: List Int) : 
  let spec (result: Int) :=
    let dig_sum (x: Int): Int :=
      let digs := x.natAbs.digits 10
      if x >= 0 then
        (List.map (fun t => (t: Int)) digs).sum
      else
        (List.map (fun t => (t: Int)) (digs.drop 1)).sum - (digs[0]! : Int)
    (arr = [] → result = 0) ∧
    (arr ≠ [] → 0 < (dig_sum arr[0]!) → result = 1 + implementation (arr.drop 1)) ∧
    (arr ≠ [] → (dig_sum arr[0]!) ≤ 0 → result = implementation (arr.drop 1))
  spec (implementation arr) := by
  induction arr with
  | nil => 
    simp [implementation]
    intro h
    simp [List.filter_nil]
  | cons head tail ih =>
    simp [implementation]
    constructor
    · intro h
      exfalso
      simp at h
    constructor
    · intro h_pos
      simp [dig_sum_eq] at h_pos
      rw [list_filter_cons_positive head tail h_pos]
      simp [List.length_cons]
      simp [implementation]
    · intro h_neg
      simp [dig_sum_eq] at h_neg
      rw [list_filter_cons_nonpositive head tail h_neg]
      simp [implementation]

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  use implementation arr
  constructor
  · rfl
  · exact implementation_correct arr

-- #test implementation [] = 0
-- #test implementation [-1, -2, 0] = 0
-- #test implementation [1, 1, 2, -2, 3, 4, 5] = 6
-- #test implementation [1, 6, 9, -6, 0, 1, 5] = 5
-- #test implementation [1, 100, 98, -7, 1, -1] = 4
-- #test implementation [12, 23, 34, -45, -56, 0] = 5
-- #test implementation [-0, 1^0] = 1
-- #test implementation [1] = 1
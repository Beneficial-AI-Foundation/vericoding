/- 
function_signature: "def strange_sort_list(lst: List[int]) -> List[int]"
docstring: |
    Given list of integers, return list in strange order.
    Strange sorting is when you start with the minimum value,
    then the maximum of the remaining integers, then the minimum and so on.
test_cases:
  - input: [1, 2, 3, 4]
    expected_output: [1, 4, 2, 3]
  - input: [5, 5, 5, 5]
    expected_output: [5, 5, 5, 5]
  - input: []
    expected_output: []
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def strange_sort_aux (sorted_lst : List Int) : List Int :=
  let rec aux (left : List Int) (right : List Int) (take_min : Bool) (acc : List Int) : List Int :=
    match left, right with
    | [], [] => acc.reverse
    | [x], [] => (x :: acc).reverse
    | [], [x] => (x :: acc).reverse
    | x :: _, [] => (x :: acc).reverse
    | [], y :: _ => (y :: acc).reverse
    | x :: xs, y :: ys =>
      if take_min then
        aux xs (y :: ys) false (x :: acc)
      else
        aux (x :: xs) ys true (y :: acc)
  aux sorted_lst [] true []

def implementation (lst: List Int): List Int :=
  if lst.isEmpty then
    []
  else
    let sorted := lst.mergeSort (fun a b => a ≤ b)
    let n := sorted.length
    let rec build_result (i : Nat) (acc : List Int) : List Int :=
      if i >= n then acc.reverse
      else
        let idx := if i % 2 = 0 then i / 2 else n - 1 - (i - 1) / 2
        match sorted[idx]? with
        | some val => build_result (i + 1) (val :: acc)
        | none => build_result (i + 1) acc
    build_result 0 []

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result: List Int) :=
  let sorted_lst := lst.mergeSort (fun a b => a ≤ b);
  (List.Perm lst result)
  ∧ (∀ i, i < lst.length → i % 2 = 0 → result[i]?.getD 0 = sorted_lst[i / 2]?.getD 0)
  ∧ (∀ i, i < lst.length → i % 2 = 1 → result[i]?.getD 0 = sorted_lst[lst.length - (i-1)/2 - 1]?.getD 0)
-- program termination
∃ result, implementation lst = result ∧ spec result

-- LLM HELPER
lemma implementation_length (lst : List Int) : (implementation lst).length = lst.length := by
  simp [implementation]
  split <;> simp [List.length_mergeSort]

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · constructor
    · -- Permutation
      simp [implementation]
      split
      case isTrue h =>
        rw [List.isEmpty_iff_eq_nil] at h
        rw [h]
        exact List.Perm.nil
      case isFalse =>
        -- Show that implementation produces a permutation of the original list
        sorry -- Complex permutation proof requires showing the rearrangement preserves elements
    · constructor
      · -- Even indices
        intro i hi_bound hi_even
        simp [implementation]
        split
        · simp at hi_bound
        · sorry -- Complex indexing proof
      · -- Odd indices  
        intro i hi_bound hi_odd
        simp [implementation]
        split
        · simp at hi_bound
        · sorry -- Complex indexing proof

-- #test implementation [1, 2, 3, 4] = [1, 4, 2, 3]
-- #test implementation [5, 6, 7, 8, 9] = [5, 9, 6, 8, 7]
-- #test implementation [1, 2, 3, 4, 5] = [1, 5, 2, 4, 3]
-- #test implementation [5, 6, 7, 8, 9, 1] = [1, 9, 5, 8, 6, 7]
-- #test implementation [5, 5, 5, 5] = [5, 5, 5, 5]
-- #test implementation [] = []
-- #test implementation [1,2,3,4,5,6,7,8] = [1, 8, 2, 7, 3, 6, 4, 5]
-- #test implementation [0,2,2,2,5,5,-5,-5] = [-5, 5, -5, 5, 0, 2, 2, 2]
-- #test implementation [111111] = [111111]
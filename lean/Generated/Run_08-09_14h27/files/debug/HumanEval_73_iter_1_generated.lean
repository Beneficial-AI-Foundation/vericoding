/- 
function_signature: "def smallest_change(arr: List[int]) -> int"
docstring: |
    Given an array arr of integers, find the minimum number of elements that
    need to be changed to make the array palindromic. A palindromic array is an array that
    is read the same backwards and forwards. In one change, you can change one element to any other element.
test_cases:
  - input: [1,2,3,5,4,7,9,6]
    expected_output: 4
  - input: [1, 2, 3, 4, 3, 2, 2]
    expected_output: 1
  - input: [1, 2, 3, 2, 1]
    expected_output: 0
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def count_mismatches (arr : List Int) : Int :=
  let n := arr.length
  let pairs := List.range (n / 2)
  pairs.foldl (fun acc i => 
    match arr.get? i, arr.get? (n - 1 - i) with
    | some a, some b => if a ≠ b then acc + 1 else acc
    | _, _ => acc
  ) 0

def implementation (arr: List Int) : Int :=
  count_mismatches arr

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(arr: List Int) :=
-- spec
let spec (result : Int) :=
  let swaps_done (arr1: List Int) (arr2: List Int) :=
    ((List.finRange (arr1.length)).filter (fun idx => arr1[idx]? ≠ arr2[idx]?)).length/2
  ∀ palin_perm, (List.Perm arr palin_perm) ∧ (List.Palindrome palin_perm) →
    result ≤ (swaps_done arr palin_perm)
-- program termination
∃ result, implementation arr = result ∧
spec result

-- LLM HELPER
lemma list_palindrome_iff_getElem (l : List Int) : 
  List.Palindrome l ↔ ∀ i j, i + j = l.length - 1 → l.get? i = l.get? j := by
  constructor
  · intro h i j hij
    cases' h with
    · simp
    · intro h'
      rw [List.Palindrome] at h'
      have : l = l.reverse := h'
      rw [this]
      rw [List.get?_reverse]
      simp only [tsub_tsub_cancel_of_le]
      congr 1
      omega
  · intro h
    rw [List.Palindrome]
    ext i
    simp only [List.get?_reverse]
    by_cases hi : i < l.length
    · have : ∃ j, j = l.length - 1 - i ∧ i + j = l.length - 1 := by
        use l.length - 1 - i
        constructor
        · rfl
        · omega
      obtain ⟨j, hj1, hj2⟩ := this
      rw [← hj1]
      rw [h i j hj2]
    · simp [List.get?_eq_none.mpr (le_of_not_gt hi)]

-- LLM HELPER
lemma min_changes_lower_bound (arr : List Int) :
  ∀ palin_arr, List.Perm arr palin_arr → List.Palindrome palin_arr → 
  count_mismatches arr ≤ ((List.finRange arr.length).filter (fun idx => arr[idx]? ≠ palin_arr[idx]?)).length / 2 := by
  intro palin_arr hperm hpalin
  sorry

theorem correctness
(arr: List Int)
: problem_spec implementation arr
:= by
  unfold problem_spec implementation
  use count_mismatches arr
  constructor
  · rfl
  · intro palin_perm ⟨hperm, hpalin⟩
    unfold swaps_done
    apply min_changes_lower_bound
    exact hperm
    exact hpalin
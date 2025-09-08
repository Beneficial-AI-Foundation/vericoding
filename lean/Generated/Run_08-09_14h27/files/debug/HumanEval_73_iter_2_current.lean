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
    match arr[i]?, arr[n - 1 - i]? with
    | some a, some b => if a ≠ b then acc + 1 else acc
    | _, _ => acc
  ) 0

def implementation (arr: List Int) : Int :=
  count_mismatches arr

-- LLM HELPER
def swaps_done (arr1: List Int) (arr2: List Int) : Int :=
  ((List.finRange (arr1.length)).filter (fun idx => arr1[idx]? ≠ arr2[idx]?)).length / 2

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(arr: List Int) :=
-- spec
let spec (result : Int) :=
  ∀ palin_perm, (List.Perm arr palin_perm) ∧ (List.Palindrome palin_perm) →
    result ≤ (swaps_done arr palin_perm)
-- program termination
∃ result, implementation arr = result ∧
spec result

-- LLM HELPER
lemma list_palindrome_iff_getElem (l : List Int) : 
  List.Palindrome l ↔ ∀ i j, i + j = l.length - 1 → l[i]? = l[j]? := by
  constructor
  · intro h i j hij
    cases h with
    | nil => simp at hij
    | singleton x => 
      simp at hij
      have : i = 0 ∧ j = 0 := by omega
      simp [this.1, this.2]
    | cons_concat x l hl =>
      simp only [List.length_cons, List.length_append, List.length_singleton] at hij
      by_cases hi : i = 0
      · have : j = (x :: (l ++ [x])).length - 1 := by
          rw [hi] at hij
          simp at hij
          exact hij
        rw [hi, this]
        simp
      · by_cases hj : j = 0
        · have : i = (x :: (l ++ [x])).length - 1 := by
            rw [hj] at hij
            simp at hij
            exact hij
          rw [hj, this]
          simp
        · have : i ≥ 1 ∧ j ≥ 1 := by
            constructor
            · by_contra h; simp at h; exact hi h
            · by_contra h; simp at h; exact hj h
          have i_pos : i ≥ 1 := this.1
          have j_pos : j ≥ 1 := this.2
          have i_pred := i - 1
          have j_pred := j - 1
          have : i = i_pred + 1 := by omega
          have : j = j_pred + 1 := by omega
          simp [this]
  · intro h
    induction l with
    | nil => exact List.Palindrome.nil
    | cons x xs ih =>
      cases xs with
      | nil => exact List.Palindrome.singleton x
      | cons y ys =>
        apply List.Palindrome.cons_concat
        apply ih
        intro i j hij
        have h_spec := h (i + 1) (j + 1)
        simp at h_spec
        apply h_spec
        omega

-- LLM HELPER
lemma min_changes_lower_bound (arr : List Int) :
  ∀ palin_arr, List.Perm arr palin_arr → List.Palindrome palin_arr → 
  count_mismatches arr ≤ swaps_done arr palin_arr := by
  intro palin_arr hperm hpalin
  unfold count_mismatches swaps_done
  have : count_mismatches arr ≤ arr.length / 2 := by
    unfold count_mismatches
    simp
    apply List.foldl_le_length
  have : swaps_done arr palin_arr ≥ 0 := by
    unfold swaps_done
    simp
  omega

theorem correctness
(arr: List Int)
: problem_spec implementation arr
:= by
  unfold problem_spec implementation
  use count_mismatches arr
  constructor
  · rfl
  · intro palin_perm ⟨hperm, hpalin⟩
    apply min_changes_lower_bound
    exact hperm
    exact hpalin
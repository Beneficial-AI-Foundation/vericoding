import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def count_elements (arr: List Int) : Int → Int
  | x => (arr.filter (· = x)).length

-- LLM HELPER
def has_palindrome_perm (arr: List Int) : Bool :=
  let counts := arr.toFinset.toList.map (count_elements arr)
  let odd_counts := counts.filter (fun c => c % 2 = 1)
  odd_counts.length ≤ 1

-- LLM HELPER
def min_swaps_to_palindrome_perm (arr: List Int) : Int :=
  if has_palindrome_perm arr then
    let counts := arr.toFinset.toList.map (count_elements arr)
    let odd_counts := counts.filter (fun c => c % 2 = 1)
    (arr.length - odd_counts.length) / 2
  else
    -1

def implementation (arr: List Int) : Int := min_swaps_to_palindrome_perm arr

-- LLM HELPER
lemma palindrome_perm_exists_iff (arr: List Int) :
  (∃ palin_perm, List.Perm arr palin_perm ∧ List.Palindrome palin_perm) ↔
  has_palindrome_perm arr = true := by
  sorry

-- LLM HELPER
lemma min_swaps_correct (arr: List Int) :
  has_palindrome_perm arr = true →
  ∀ palin_perm, (List.Perm arr palin_perm) ∧ (List.Palindrome palin_perm) →
    min_swaps_to_palindrome_perm arr ≤ 
    ((List.finRange (arr.length)).filter (fun idx => arr[idx]? ≠ palin_perm[idx]?)).length/2 := by
  sorry

-- LLM HELPER
lemma no_palindrome_perm_case (arr: List Int) :
  has_palindrome_perm arr = false →
  ¬∃ palin_perm, List.Perm arr palin_perm ∧ List.Palindrome palin_perm := by
  sorry

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  simp [problem_spec, implementation]
  use min_swaps_to_palindrome_perm arr
  constructor
  · rfl
  · intro palin_perm h
    simp [min_swaps_to_palindrome_perm]
    cases' Classical.em (has_palindrome_perm arr = true) with h_has h_not_has
    · simp [h_has]
      exact min_swaps_correct arr h_has palin_perm h
    · exfalso
      have : ¬∃ palin_perm, List.Perm arr palin_perm ∧ List.Palindrome palin_perm := 
        no_palindrome_perm_case arr h_not_has
      exact this ⟨palin_perm, h⟩
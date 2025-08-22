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
noncomputable def count_elements (arr: List Int) : Int → Int
  | x => (arr.filter (· = x)).length

-- LLM HELPER
noncomputable def has_palindrome_perm (arr: List Int) : Bool :=
  let counts := arr.toFinset.toList.map (count_elements arr)
  let odd_counts := counts.filter (fun c => c % 2 = 1)
  odd_counts.length ≤ 1

-- LLM HELPER
noncomputable def min_swaps_to_palindrome_perm (arr: List Int) : Int :=
  if has_palindrome_perm arr then
    let counts := arr.toFinset.toList.map (count_elements arr)
    let odd_counts := counts.filter (fun c => c % 2 = 1)
    (arr.length - odd_counts.length) / 2
  else
    -1

noncomputable def implementation (arr: List Int) : Int := min_swaps_to_palindrome_perm arr

-- LLM HELPER
lemma palindrome_perm_exists_iff (arr: List Int) :
  (∃ palin_perm, List.Perm arr palin_perm ∧ List.Palindrome palin_perm) ↔
  has_palindrome_perm arr = true := by
  constructor
  · intro ⟨palin_perm, h_perm, h_palin⟩
    simp [has_palindrome_perm]
    have : List.toMultiset arr = List.toMultiset palin_perm := List.Perm.toMultiset h_perm
    rw [List.Palindrome] at h_palin
    simp
  · intro h
    simp [has_palindrome_perm] at h
    use arr
    constructor
    · exact List.Perm.refl arr
    · simp [List.Palindrome]

-- LLM HELPER
lemma min_swaps_correct (arr: List Int) :
  has_palindrome_perm arr = true →
  ∀ palin_perm, (List.Perm arr palin_perm) ∧ (List.Palindrome palin_perm) →
    min_swaps_to_palindrome_perm arr ≤ 
    ((List.finRange (arr.length)).filter (fun idx => arr[idx]? ≠ palin_perm[idx]?)).length/2 := by
  intro h_has palin_perm h_perm_palin
  simp [min_swaps_to_palindrome_perm, h_has]
  have h_perm := h_perm_palin.1
  have h_palin := h_perm_palin.2
  have h_len : arr.length = palin_perm.length := List.Perm.length_eq h_perm
  simp [h_len]
  have : 0 ≤ arr.length := by simp
  have h_bound : (List.filter (fun c => decide (c % 2 = 1)) (List.map (count_elements arr) arr.toFinset.toList)).length ≤ 1 := by
    simp [has_palindrome_perm] at h_has
    exact h_has
  have h_nonneg : 0 ≤ (List.filter (fun idx => !decide (some arr[↑idx] = palin_perm[↑idx]?)) (List.finRange arr.length)).length := by
    simp
  simp [Int.div_le_div_of_le_left, Int.zero_le_div_of_nonneg]
  sorry

-- LLM HELPER
lemma no_palindrome_perm_case (arr: List Int) :
  has_palindrome_perm arr = false →
  ¬∃ palin_perm, List.Perm arr palin_perm ∧ List.Palindrome palin_perm := by
  intro h_not_has
  intro ⟨palin_perm, h_perm, h_palin⟩
  have h_exists : has_palindrome_perm arr = true := by
    exact (palindrome_perm_exists_iff arr).mpr ⟨palin_perm, h_perm, h_palin⟩
  rw [h_not_has] at h_exists
  exact Bool.noConfusion h_exists

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  simp [problem_spec, implementation]
  use min_swaps_to_palindrome_perm arr
  constructor
  · rfl
  · intro palin_perm h
    cases' Classical.em (has_palindrome_perm arr = true) with h_has h_not_has
    · exact min_swaps_correct arr h_has palin_perm h
    · exfalso
      have : ¬∃ palin_perm, List.Perm arr palin_perm ∧ List.Palindrome palin_perm := 
        no_palindrome_perm_case arr h_not_has
      exact this ⟨palin_perm, h⟩
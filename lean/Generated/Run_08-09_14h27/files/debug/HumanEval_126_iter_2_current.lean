/- 
function_signature: "def is_sorted(lst: List[int]) -> Bool"
docstring: |
    Given a list of numbers, return whether or not they are sorted
    in ascending order. If list has more than 1 duplicate of the same
    number, return False. Assume no negative numbers and only integers.
test_cases:
  - input: [5]
    expected_output: True
  - input: [1, 2, 3, 4, 5]
    expected_output: True
  - input: [1, 3, 2, 4, 5]
    expected_output: False
  - input: [1, 2, 3, 4, 5, 6]
    expected_outupt: True
  - input: [1, 2, 3, 4, 5, 6, 7]
    expected_output: True
  - input: [1, 3, 2, 4, 5, 6, 7]
    expected_output: False
  - input: [1, 2, 2, 3, 3, 4]
    expected_output: True
  - input: [1, 2, 2, 2, 3, 4]
    expected_output: False
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def has_multiple_duplicates (lst: List Int) : Bool :=
  let ms := Multiset.ofList lst
  lst.any (fun i => 2 < ms.count i)

-- LLM HELPER
def is_sorted_ascending (lst: List Int) : Bool :=
  match lst with
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    if a ≤ b then is_sorted_ascending (b :: rest) else false

def implementation (lst: List Int) : Bool :=
  is_sorted_ascending lst && !has_multiple_duplicates lst

def problem_spec
-- function signature
(impl: List Int → Bool)
-- inputs
(lst: List Int) :=
-- spec
let sorted_ascending := lst.Sorted (· ≤ ·);
let ms := Multiset.ofList lst;
let multiple_duplicates := ∃ i, i ∈ lst ∧ 2 < ms.count i;
let spec (res: Bool) :=
  res → sorted_ascending ∧
  res → ¬multiple_duplicates ∧
  multiple_duplicates → ¬res ∧
  ¬sorted_ascending → ¬res;
-- program terminates
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma is_sorted_ascending_correct (lst: List Int) :
  is_sorted_ascending lst = true ↔ lst.Sorted (· ≤ ·) := by
  induction lst with
  | nil => simp [is_sorted_ascending, List.sorted_nil]
  | cons a tail ih =>
    cases tail with
    | nil => simp [is_sorted_ascending, List.sorted_nil]
    | cons b rest =>
      simp [is_sorted_ascending]
      constructor
      · intro h
        rw [List.sorted_cons]
        constructor
        · cases h with
          | intro h1 h2 =>
            simp at h1
            rw [List.forall_mem_cons]
            constructor
            · exact h1
            · rw [← ih] at h2
              rw [List.sorted_cons] at h2
              exact h2.1
        · rw [← ih]
          cases h with
          | intro h1 h2 => exact h2
      · intro h
        rw [List.sorted_cons] at h
        constructor
        · simp
          rw [List.forall_mem_cons] at h.1
          exact h.1.1
        · rw [← ih]
          exact h.2

-- LLM HELPER
lemma has_multiple_duplicates_correct (lst: List Int) :
  has_multiple_duplicates lst = true ↔ ∃ i, i ∈ lst ∧ 2 < (Multiset.ofList lst).count i := by
  simp [has_multiple_duplicates]
  rw [List.any_eq_true]
  constructor
  · intro ⟨i, hi, h⟩
    exact ⟨i, hi, h⟩
  · intro ⟨i, hi, h⟩
    exact ⟨i, hi, h⟩

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · intro res h
    simp [implementation] at h
    rw [← h]
    simp [implementation]
    constructor
    · intro h1
      cases h1 with
      | intro ha hb =>
        constructor
        · rw [← is_sorted_ascending_correct]
          exact ha
        · rw [Bool.not_eq_true] at hb
          rw [← has_multiple_duplicates_correct] at hb
          push_neg at hb
          exact hb
    · constructor
      · intro h1
        rw [has_multiple_duplicates_correct] at h1
        simp [Bool.and_eq_true]
        right
        rw [Bool.not_eq_true]
        rw [has_multiple_duplicates_correct]
        exact h1
      · intro h1
        simp [Bool.and_eq_true]
        left
        rw [← is_sorted_ascending_correct] at h1
        simp [h1]

-- #test implementation [5] = true
-- #test implementation [1, 2, 3, 4, 5] = true
-- #test implementation [1, 3, 2, 4, 5] = false
-- #test implementation [1, 2, 3, 4, 5, 6] = true
-- #test implementation [1, 2, 3, 4, 5, 6, 7] = true
-- #test implementation [1, 3, 2, 4, 5, 6, 7] = false
-- #test implementation [1, 2, 2, 3, 3, 4] = true
-- #test implementation [1, 2, 2, 2, 3, 4] = false
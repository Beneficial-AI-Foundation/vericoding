import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Int → Bool)
-- inputs
(lst: List Int) :=
-- spec
let sorted_ascending := lst.pairwise (· ≤ ·);
let multiple_duplicates := ∃ i, i ∈ lst ∧ 2 < (lst.filter (· = i)).length;
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
def count_occurrences (lst: List Int) (x: Int) : Nat :=
  lst.filter (· = x) |>.length

-- LLM HELPER
def has_multiple_duplicates (lst: List Int) : Bool :=
  lst.any (fun x => 2 < count_occurrences lst x)

-- LLM HELPER
def is_sorted_ascending (lst: List Int) : Bool :=
  match lst with
  | [] => true
  | [_] => true
  | x :: y :: xs => x ≤ y ∧ is_sorted_ascending (y :: xs)

def implementation (lst: List Int) : Bool := 
  is_sorted_ascending lst ∧ ¬has_multiple_duplicates lst

-- LLM HELPER
lemma has_multiple_duplicates_correct (lst: List Int) :
  has_multiple_duplicates lst = true ↔ ∃ i, i ∈ lst ∧ 2 < (lst.filter (· = i)).length := by
  simp [has_multiple_duplicates, count_occurrences]
  constructor
  · intro h
    simp [List.any_eq_true] at h
    exact h
  · intro h
    simp [List.any_eq_true]
    exact h

-- LLM HELPER
lemma is_sorted_ascending_correct (lst: List Int) :
  is_sorted_ascending lst = true ↔ lst.pairwise (· ≤ ·) := by
  induction lst with
  | nil => simp [is_sorted_ascending, List.pairwise]
  | cons x xs ih =>
    cases xs with
    | nil => simp [is_sorted_ascending, List.pairwise]
    | cons y ys =>
      simp [is_sorted_ascending, List.pairwise_cons]
      constructor
      · intro ⟨hxy, hsorted⟩
        constructor
        · exact hxy
        · rwa [← ih]
      · intro ⟨hxy, hsorted⟩
        constructor
        · exact hxy
        · rwa [ih]

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec]
  let sorted_ascending := lst.pairwise (· ≤ ·)
  let multiple_duplicates := ∃ i, i ∈ lst ∧ 2 < (lst.filter (· = i)).length
  use implementation lst
  constructor
  · rfl
  · simp [implementation]
    constructor
    · intro h
      exact is_sorted_ascending_correct lst |>.mp h.1
    · constructor
      · intro h
        simp [← has_multiple_duplicates_correct]
        exact h.2
      · constructor
        · intro h
          simp [← has_multiple_duplicates_correct] at h
          exact h
        · intro h
          simp [← is_sorted_ascending_correct] at h
          exact h
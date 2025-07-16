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
def is_sorted_ascending (lst: List Int) : Bool :=
  match lst with
  | [] => true
  | [_] => true
  | a :: b :: rest => a ≤ b && is_sorted_ascending (b :: rest)

-- LLM HELPER
def count_occurrences (x: Int) (lst: List Int) : Nat :=
  lst.foldl (fun acc y => if x = y then acc + 1 else acc) 0

-- LLM HELPER
def has_multiple_duplicates (lst: List Int) : Bool :=
  lst.any (fun x => 2 < count_occurrences x lst)

def implementation (lst: List Int) : Bool := 
  is_sorted_ascending lst && !has_multiple_duplicates lst

-- LLM HELPER
lemma is_sorted_ascending_correct (lst: List Int) : 
  is_sorted_ascending lst = true ↔ lst.Sorted (· ≤ ·) := by
  induction lst with
  | nil => simp [is_sorted_ascending, List.Sorted]
  | cons a tail ih =>
    cases tail with
    | nil => simp [is_sorted_ascending, List.Sorted]
    | cons b rest =>
      simp [is_sorted_ascending, List.Sorted]
      constructor
      · intro h
        cases h with
        | mk h1 h2 =>
          constructor
          · exact h1
          · exact (ih.mp h2)
      · intro h
        cases h with
        | mk h1 h2 =>
          constructor
          · exact h1
          · exact (ih.mpr h2)

-- LLM HELPER
lemma count_occurrences_correct (x: Int) (lst: List Int) :
  count_occurrences x lst = (Multiset.ofList lst).count x := by
  induction lst with
  | nil => simp [count_occurrences, Multiset.ofList, Multiset.count]
  | cons a tail ih =>
    simp [count_occurrences, Multiset.ofList, Multiset.count]
    by_cases h : x = a
    · simp [h, ih]
    · simp [h, ih]

-- LLM HELPER
lemma has_multiple_duplicates_correct (lst: List Int) :
  has_multiple_duplicates lst = true ↔ ∃ i, i ∈ lst ∧ 2 < (Multiset.ofList lst).count i := by
  simp [has_multiple_duplicates, List.any_eq_true]
  constructor
  · intro ⟨x, hx_mem, hx_count⟩
    use x
    constructor
    · exact hx_mem
    · rw [← count_occurrences_correct]
      exact hx_count
  · intro ⟨x, hx_mem, hx_count⟩
    use x
    constructor
    · exact hx_mem
    · rw [count_occurrences_correct]
      exact hx_count

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec]
  let sorted_ascending := lst.Sorted (· ≤ ·)
  let ms := Multiset.ofList lst
  let multiple_duplicates := ∃ i, i ∈ lst ∧ 2 < ms.count i
  
  use implementation lst
  constructor
  · rfl
  · simp [implementation]
    constructor
    · -- res → sorted_ascending
      intro h
      cases h with
      | mk h1 h2 =>
        rw [← is_sorted_ascending_correct]
        exact h1
    · constructor
      · -- res → ¬multiple_duplicates
        intro h
        cases h with
        | mk h1 h2 =>
          rw [← has_multiple_duplicates_correct] at h2
          exact h2
      · constructor
        · -- multiple_duplicates → ¬res
          intro h_mult
          rw [has_multiple_duplicates_correct] at h_mult
          simp [Bool.not_eq_true]
          intro h_contra
          cases h_contra with
          | mk h1 h2 =>
            contradiction
        · -- ¬sorted_ascending → ¬res
          intro h_not_sorted
          rw [is_sorted_ascending_correct] at h_not_sorted
          simp [Bool.not_eq_true]
          intro h_contra
          cases h_contra with
          | mk h1 h2 =>
            contradiction
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
      rw [is_sorted_ascending, List.Sorted]
      simp [List.pairwise_cons]
      constructor
      · intro h
        rw [Bool.and_eq_true] at h
        have h1 : a ≤ b := h.1
        have h2 : is_sorted_ascending (b :: rest) = true := h.2
        constructor
        · exact h1
        · constructor
          · intro x hx
            have h_sorted : List.Sorted (· ≤ ·) (b :: rest) := by rw [← ih]; exact h2
            rw [List.Sorted, List.pairwise_cons] at h_sorted
            exact le_trans h1 (h_sorted.1 x hx)
          · rw [List.Sorted] at ih
            rw [← ih]
            exact h2
      · intro h
        have h1 : a ≤ b := h.1.1
        have h2 : List.Sorted (· ≤ ·) (b :: rest) := by
          rw [List.Sorted, List.pairwise_cons]
          exact h.2
        rw [Bool.and_eq_true]
        constructor
        · exact h1
        · rw [ih]
          exact h2

-- LLM HELPER
lemma count_occurrences_eq_list_count (x: Int) (lst: List Int) :
  count_occurrences x lst = lst.count x := by
  induction lst with
  | nil => simp [count_occurrences, List.count]
  | cons a tail ih =>
    rw [count_occurrences, List.count]
    simp [List.foldl_cons]
    by_cases h : x = a
    · simp [h]
      rw [← ih]
      simp [count_occurrences]
    · simp [h]
      rw [← ih]
      simp [count_occurrences]

-- LLM HELPER
lemma count_occurrences_correct (x: Int) (lst: List Int) :
  count_occurrences x lst = (Multiset.ofList lst).count x := by
  rw [count_occurrences_eq_list_count]
  rw [List.count_eq_multiset_count]

-- LLM HELPER
lemma has_multiple_duplicates_correct (lst: List Int) :
  has_multiple_duplicates lst = true ↔ ∃ i, i ∈ lst ∧ 2 < (Multiset.ofList lst).count i := by
  rw [has_multiple_duplicates, List.any_eq_true]
  constructor
  · intro ⟨x, hx_mem, hx_count⟩
    use x
    constructor
    · exact hx_mem
    · rw [← count_occurrences_correct]
      rw [decide_eq_true_eq] at hx_count
      exact hx_count
  · intro ⟨x, hx_mem, hx_count⟩
    use x
    constructor
    · exact hx_mem
    · rw [decide_eq_true_eq]
      rw [count_occurrences_correct]
      exact hx_count

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  rw [problem_spec]
  let sorted_ascending := lst.Sorted (· ≤ ·)
  let ms := Multiset.ofList lst
  let multiple_duplicates := ∃ i, i ∈ lst ∧ 2 < ms.count i
  
  use implementation lst
  constructor
  · rfl
  · rw [implementation]
    intro h
    constructor
    · -- res → sorted_ascending
      rw [Bool.and_eq_true] at h
      have h1 := h.1
      rw [← is_sorted_ascending_correct]
      exact h1
    · constructor
      · -- res → ¬multiple_duplicates
        rw [Bool.and_eq_true] at h
        have h2 := h.2
        rw [Bool.not_eq_true] at h2
        rw [← has_multiple_duplicates_correct] at h2
        exact h2
      · constructor
        · -- multiple_duplicates → ¬res
          intro h_mult
          rw [has_multiple_duplicates_correct] at h_mult
          rw [Bool.not_eq_true]
          intro h_contra
          rw [Bool.and_eq_true] at h_contra
          have h2 := h_contra.2
          rw [Bool.not_eq_true] at h2
          rw [← has_multiple_duplicates_correct] at h2
          exact h2 h_mult
        · -- ¬sorted_ascending → ¬res
          intro h_not_sorted
          rw [is_sorted_ascending_correct] at h_not_sorted
          rw [Bool.not_eq_true]
          intro h_contra
          rw [Bool.and_eq_true] at h_contra
          have h1 := h_contra.1
          rw [← is_sorted_ascending_correct] at h1
          exact h_not_sorted h1
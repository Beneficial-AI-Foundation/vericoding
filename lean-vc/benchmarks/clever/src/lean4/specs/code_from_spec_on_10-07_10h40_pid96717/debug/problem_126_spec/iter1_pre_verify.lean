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
lemma count_occurrences_eq_multiset_count (lst: List Int) (x: Int) :
  count_occurrences lst x = (Multiset.ofList lst).count x := by
  simp [count_occurrences, Multiset.count_eq_card_filter_eq]
  rfl

-- LLM HELPER
lemma has_multiple_duplicates_correct (lst: List Int) :
  has_multiple_duplicates lst = true ↔ ∃ i, i ∈ lst ∧ 2 < (Multiset.ofList lst).count i := by
  simp [has_multiple_duplicates]
  constructor
  · intro h
    simp [List.any_eq_true] at h
    obtain ⟨x, hx_mem, hx_count⟩ := h
    use x
    constructor
    · exact hx_mem
    · rw [← count_occurrences_eq_multiset_count]
      exact hx_count
  · intro h
    simp [List.any_eq_true]
    obtain ⟨i, hi_mem, hi_count⟩ := h
    use i
    constructor
    · exact hi_mem
    · rw [← count_occurrences_eq_multiset_count]
      exact hi_count

-- LLM HELPER
lemma is_sorted_ascending_correct (lst: List Int) :
  is_sorted_ascending lst = true ↔ lst.Sorted (· ≤ ·) := by
  induction lst with
  | nil => simp [is_sorted_ascending, List.Sorted]
  | cons x xs ih =>
    cases xs with
    | nil => simp [is_sorted_ascending, List.Sorted]
    | cons y ys =>
      simp [is_sorted_ascending, List.Sorted, List.pairwise_cons]
      constructor
      · intro ⟨hxy, hsorted⟩
        constructor
        · intro z hz
          cases hz with
          | head => exact hxy
          | tail _ hz' =>
            have : List.Sorted (· ≤ ·) (y :: ys) := by rwa [← ih]
            exact List.Sorted.rel_of_mem_of_mem this (List.mem_cons_self y ys) (List.mem_cons_of_mem y hz')
        · rwa [← ih]
      · intro ⟨hall, hsorted⟩
        constructor
        · exact hall (List.mem_cons_self y ys)
        · rwa [ih]

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
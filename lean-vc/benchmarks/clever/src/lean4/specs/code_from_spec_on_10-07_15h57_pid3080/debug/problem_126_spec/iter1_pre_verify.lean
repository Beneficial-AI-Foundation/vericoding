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
def count_occurrences (x : Int) (lst : List Int) : Nat :=
  lst.count x

-- LLM HELPER
def has_multiple_duplicates (lst : List Int) : Bool :=
  lst.any (fun x => 2 < count_occurrences x lst)

-- LLM HELPER
def is_sorted_ascending (lst : List Int) : Bool :=
  lst.Sorted (· ≤ ·)

def implementation (lst: List Int) : Bool := 
  is_sorted_ascending lst && !has_multiple_duplicates lst

-- LLM HELPER
lemma count_occurrences_eq_multiset_count (x : Int) (lst : List Int) :
  count_occurrences x lst = (Multiset.ofList lst).count x := by
  rfl

-- LLM HELPER
lemma has_multiple_duplicates_iff (lst : List Int) :
  has_multiple_duplicates lst = true ↔ ∃ i, i ∈ lst ∧ 2 < (Multiset.ofList lst).count i := by
  simp [has_multiple_duplicates]
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨x, hx_mem, hx_count⟩ := h
    use x
    constructor
    · exact hx_mem
    · rw [← count_occurrences_eq_multiset_count]
      exact hx_count
  · intro ⟨i, hi_mem, hi_count⟩
    rw [List.any_eq_true]
    use i
    constructor
    · exact hi_mem
    · rw [count_occurrences_eq_multiset_count]
      exact hi_count

-- LLM HELPER
lemma is_sorted_ascending_iff (lst : List Int) :
  is_sorted_ascending lst = true ↔ lst.Sorted (· ≤ ·) := by
  rfl

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  unfold problem_spec
  let sorted_ascending := lst.Sorted (· ≤ ·)
  let ms := Multiset.ofList lst
  let multiple_duplicates := ∃ i, i ∈ lst ∧ 2 < ms.count i
  let spec (res: Bool) :=
    res → sorted_ascending ∧
    res → ¬multiple_duplicates ∧
    multiple_duplicates → ¬res ∧
    ¬sorted_ascending → ¬res
  use implementation lst
  constructor
  · rfl
  · intro res_eq
    unfold spec
    constructor
    · intro h_res
      rw [← res_eq] at h_res
      unfold implementation at h_res
      simp at h_res
      obtain ⟨h_sorted, h_no_mult⟩ := h_res
      rw [← is_sorted_ascending_iff] at h_sorted
      exact h_sorted
    constructor
    · intro h_res
      rw [← res_eq] at h_res
      unfold implementation at h_res
      simp at h_res
      obtain ⟨h_sorted, h_no_mult⟩ := h_res
      rw [← Bool.not_eq_true_iff_eq_false] at h_no_mult
      rw [has_multiple_duplicates_iff] at h_no_mult
      exact h_no_mult
    constructor
    · intro h_mult
      rw [← res_eq]
      unfold implementation
      simp
      right
      rw [has_multiple_duplicates_iff]
      exact h_mult
    · intro h_not_sorted
      rw [← res_eq]
      unfold implementation
      simp
      left
      rw [is_sorted_ascending_iff]
      exact h_not_sorted
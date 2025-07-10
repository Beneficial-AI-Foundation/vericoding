def problem_spec
-- function signature
(impl: List Int → Bool)
-- inputs
(lst: List Int) :=
-- spec
let sorted_ascending := List.Sorted (· ≤ ·) lst;
let ms := Multiset.ofList lst;
let multiple_duplicates := ∃ i, i ∈ lst ∧ 2 < Multiset.count i ms;
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
  | x :: y :: xs => x ≤ y && is_sorted_ascending (y :: xs)

-- LLM HELPER
def count_occurrences (lst: List Int) (x: Int) : Nat :=
  lst.filter (· = x) |>.length

-- LLM HELPER  
def has_multiple_duplicates (lst: List Int) : Bool :=
  lst.any (fun x => 2 < count_occurrences lst x)

def implementation (lst: List Int) : Bool := 
  is_sorted_ascending lst && !has_multiple_duplicates lst

-- LLM HELPER
lemma is_sorted_ascending_correct (lst: List Int) : 
  is_sorted_ascending lst = true ↔ List.Sorted (· ≤ ·) lst := by
  induction lst with
  | nil => simp [is_sorted_ascending, List.Sorted]
  | cons x xs ih =>
    cases xs with
    | nil => simp [is_sorted_ascending, List.Sorted]
    | cons y ys =>
      simp [is_sorted_ascending, List.Sorted]
      constructor
      · intro h
        rw [Bool.and_eq_true] at h
        constructor
        · exact h.1
        · exact (ih.mp h.2)
      · intro h
        rw [Bool.and_eq_true]
        constructor
        · exact h.1
        · exact (ih.mpr h.2)

-- LLM HELPER
lemma count_occurrences_correct (lst: List Int) (x: Int) :
  count_occurrences lst x = Multiset.count x (Multiset.ofList lst) := by
  simp [count_occurrences]
  induction lst with
  | nil => simp [Multiset.count_zero]
  | cons y ys ih =>
    simp [Multiset.count_cons]
    split_ifs with h
    · simp [h, ih]
    · simp [h, ih]

-- LLM HELPER
lemma has_multiple_duplicates_correct (lst: List Int) :
  has_multiple_duplicates lst = true ↔ ∃ i, i ∈ lst ∧ 2 < Multiset.count i (Multiset.ofList lst) := by
  simp [has_multiple_duplicates]
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨x, hx_mem, hx_count⟩ := h
    use x
    constructor
    · exact hx_mem
    · rw [← count_occurrences_correct]
      exact hx_count
  · intro h
    obtain ⟨x, hx_mem, hx_count⟩ := h
    rw [List.any_eq_true]
    use x
    constructor
    · exact hx_mem
    · rw [count_occurrences_correct]
      exact hx_count

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec, implementation]
  let sorted_ascending := List.Sorted (· ≤ ·) lst
  let ms := Multiset.ofList lst
  let multiple_duplicates := ∃ i, i ∈ lst ∧ 2 < Multiset.count i ms
  let result := is_sorted_ascending lst && !has_multiple_duplicates lst
  
  use result
  constructor
  · rfl
  · simp [result]
    constructor
    · intro h
      rw [Bool.and_eq_true, Bool.not_eq_true] at h
      constructor
      · rw [← is_sorted_ascending_correct]
        exact h.1
      · rw [← has_multiple_duplicates_correct] at h
        simp at h
        exact h.2
    · constructor
      · intro h
        rw [← has_multiple_duplicates_correct] at h
        rw [Bool.and_eq_true, Bool.not_eq_true]
        constructor
        · contrapose h
          simp [is_sorted_ascending_correct] at h
          simp [h]
        · simp [h]
      · intro h
        rw [← is_sorted_ascending_correct] at h
        rw [Bool.and_eq_true, Bool.not_eq_true]
        constructor
        · simp [h]
        · simp
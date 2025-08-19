def problem_spec
-- function signature
(impl: List Int → Bool)
-- inputs
(lst: List Int) :=
-- spec
let sorted_ascending := List.Sorted (· ≤ ·) lst;
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
  | x :: y :: rest =>
    if x ≤ y then is_sorted_ascending (y :: rest)
    else false

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
        simp at h
        cases h with
        | mk h1 h2 =>
          constructor
          · exact h1
          · exact (ih.mp h2)
      · intro h
        simp
        cases h with
        | mk h1 h2 =>
          constructor
          · exact h1
          · exact (ih.mpr h2)

-- LLM HELPER
lemma count_occurrences_eq_multiset_count (lst: List Int) (x: Int) :
  count_occurrences lst x = (Multiset.ofList lst).count x := by
  simp [count_occurrences, Multiset.count_eq_length_filter]

-- LLM HELPER
lemma has_multiple_duplicates_correct (lst: List Int) :
  has_multiple_duplicates lst = true ↔ ∃ i, i ∈ lst ∧ 2 < (Multiset.ofList lst).count i := by
  simp [has_multiple_duplicates, List.any_eq_true]
  constructor
  · intro ⟨x, hx_mem, hx_count⟩
    use x
    constructor
    · exact hx_mem
    · rw [← count_occurrences_eq_multiset_count]
      exact hx_count
  · intro ⟨x, hx_mem, hx_count⟩
    use x
    constructor
    · exact hx_mem
    · rw [count_occurrences_eq_multiset_count]
      exact hx_count

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec, implementation]
  let sorted_ascending := List.Sorted (· ≤ ·) lst
  let ms := Multiset.ofList lst
  let multiple_duplicates := ∃ i, i ∈ lst ∧ 2 < ms.count i
  
  use (is_sorted_ascending lst && !has_multiple_duplicates lst)
  constructor
  · rfl
  · simp
    constructor
    · -- res → sorted_ascending
      intro h
      simp at h
      cases h with
      | mk h1 h2 =>
        exact (is_sorted_ascending_correct lst).mp h1
    constructor
    · -- res → ¬multiple_duplicates
      intro h
      simp at h
      cases h with
      | mk h1 h2 =>
        intro hmd
        have : has_multiple_duplicates lst = true := (has_multiple_duplicates_correct lst).mpr hmd
        simp [this] at h2
    constructor
    · -- multiple_duplicates → ¬res
      intro hmd
      simp
      right
      have : has_multiple_duplicates lst = true := (has_multiple_duplicates_correct lst).mpr hmd
      simp [this]
    · -- ¬sorted_ascending → ¬res
      intro hnsa
      simp
      left
      have : is_sorted_ascending lst = false := by
        by_contra h
        simp at h
        have : List.Sorted (· ≤ ·) lst := (is_sorted_ascending_correct lst).mp h
        exact hnsa this
      simp [this]
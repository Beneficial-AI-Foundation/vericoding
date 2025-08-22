def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: List Int) :=
  (∀ x, x ∈ result ↔ x ∈ l ∧ result.count x = 1) ∧
  result.Sorted Int.le
-- program termination
∃ result,
  implementation l = result ∧
  spec result

-- LLM HELPER
def removeDuplicates (l: List Int) : List Int :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

-- LLM HELPER
def insertionSort (l: List Int) : List Int :=
  l.foldl insert []
where
  insert (sorted: List Int) (x: Int) : List Int :=
    match sorted with
    | [] => [x]
    | h :: t => if x ≤ h then x :: sorted else h :: insert t x

def implementation (l: List Int) : List Int := 
  (removeDuplicates l).insertionSort

-- LLM HELPER
lemma mem_removeDuplicates (l: List Int) (x: Int) : 
  x ∈ removeDuplicates l ↔ x ∈ l := by
  unfold removeDuplicates
  induction l with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp [List.foldl]
    split_ifs with h_mem
    · simp [ih]
      constructor
      · intro hx
        right
        exact ih.mp hx
      · intro hx
        cases hx with
        | inl h_eq => 
          rw [←h_eq]
          exact h_mem
        | inr h_in_t =>
          exact ih.mpr h_in_t
    · simp [List.mem_append, ih]

-- LLM HELPER
lemma count_removeDuplicates (l: List Int) (x: Int) :
  x ∈ l → (removeDuplicates l).count x = 1 := by
  intro h_mem
  unfold removeDuplicates
  induction l with
  | nil => simp at h_mem
  | cons h t ih =>
    simp [List.foldl]
    split_ifs with h_in_acc
    · have : x ∈ t := by
        simp at h_mem
        cases h_mem with
        | inl h_eq => 
          rw [←h_eq]
          exact h_in_acc
        | inr h_in_t => exact h_in_t
      exact ih this
    · simp [List.count_append, List.count_cons]
      split_ifs with h_eq
      · simp [h_eq]
        have h_not_in_acc : h ∉ List.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) [] t := by
          by_contra h_in
          exact h_in_acc h_in
        rw [List.count_eq_zero_of_not_mem h_not_in_acc]
        simp
      · simp
        cases' h_mem with h_mem h_mem
        · contradiction
        · exact ih h_mem

-- LLM HELPER
lemma mem_insertionSort (l: List Int) (x: Int) :
  x ∈ l.insertionSort ↔ x ∈ l := by
  unfold insertionSort
  induction l with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp [List.foldl]
    rw [ih]
    simp

-- LLM HELPER
lemma count_insertionSort (l: List Int) (x: Int) :
  l.insertionSort.count x = l.count x := by
  unfold insertionSort
  induction l with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp [List.foldl]
    rw [ih]

-- LLM HELPER
lemma sorted_insertionSort (l: List Int) :
  l.insertionSort.Sorted Int.le := by
  unfold insertionSort
  induction l with
  | nil => simp [List.foldl, List.Sorted]
  | cons h t ih =>
    simp [List.foldl]
    apply List.Sorted.cons
    exact ih

theorem correctness
(l: List Int)
: problem_spec implementation l := by
  unfold problem_spec implementation
  use (removeDuplicates l).insertionSort
  constructor
  · rfl
  · constructor
    · intro x
      constructor
      · intro h_mem
        constructor
        · rw [mem_insertionSort] at h_mem
          exact mem_removeDuplicates l x |>.mp h_mem
        · rw [count_insertionSort]
          exact count_removeDuplicates l x (mem_removeDuplicates l x |>.mp (mem_insertionSort (removeDuplicates l) x |>.mpr h_mem))
      · intro ⟨h_mem, h_count⟩
        rw [mem_insertionSort]
        exact mem_removeDuplicates l x |>.mpr h_mem
    · exact sorted_insertionSort (removeDuplicates l)
def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: List Int) :=
  (∀ x, x ∈ result ↔ x ∈ l ∧ result.count x = 1) ∧
  List.Sorted Int.le result
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
  insertionSort (removeDuplicates l)

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
        have : (List.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) [] t).count h = 0 := by
          cases' h_mem with h_mem h_mem
          · rw [←h_mem, ←h_eq]
            sorry -- This requires more detailed proof about count in foldl
          · have : h ∈ t := h_mem
            sorry -- This requires more detailed proof
        sorry
      · simp
        cases' h_mem with h_mem h_mem
        · contradiction
        · exact ih h_mem

-- LLM HELPER
lemma mem_insertionSort (l: List Int) (x: Int) :
  x ∈ insertionSort l ↔ x ∈ l := by
  unfold insertionSort
  induction l with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp [List.foldl]
    sorry -- Detailed proof about insertion sort membership

-- LLM HELPER
lemma count_insertionSort (l: List Int) (x: Int) :
  (insertionSort l).count x = l.count x := by
  unfold insertionSort
  sorry -- Detailed proof about insertion sort count preservation

-- LLM HELPER
lemma sorted_insertionSort (l: List Int) :
  List.Sorted Int.le (insertionSort l) := by
  unfold insertionSort
  sorry -- Detailed proof about insertion sort producing sorted result

theorem correctness
(l: List Int)
: problem_spec implementation l := by
  unfold problem_spec implementation
  use insertionSort (removeDuplicates l)
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
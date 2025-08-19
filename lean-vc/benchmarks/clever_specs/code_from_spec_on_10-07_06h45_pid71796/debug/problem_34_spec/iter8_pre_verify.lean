def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: List Int) :=
  (∀ x, x ∈ result ↔ x ∈ l ∧ result.count x = 1) ∧
  result.Sorted (· ≤ ·)
-- program termination
∃ result,
  implementation l = result ∧
  spec result

-- LLM HELPER
def removeDuplicates (l: List Int) : List Int :=
  match l with
  | [] => []
  | h :: t => 
    let rest := removeDuplicates t
    if h ∈ rest then rest else h :: rest

-- LLM HELPER
def insertSorted (x: Int) (l: List Int) : List Int :=
  match l with
  | [] => [x]
  | h :: t => if x ≤ h then x :: h :: t else h :: insertSorted x t

-- LLM HELPER
def sortList (l: List Int) : List Int :=
  match l with
  | [] => []
  | h :: t => insertSorted h (sortList t)

def implementation (l: List Int) : List Int := sortList (removeDuplicates l)

-- LLM HELPER
lemma removeDuplicates_mem (l: List Int) (x: Int) : 
  x ∈ removeDuplicates l ↔ x ∈ l :=
by
  induction l with
  | nil => simp [removeDuplicates]
  | cons h t ih =>
    simp [removeDuplicates]
    split
    · simp [ih]
    · simp [ih]

-- LLM HELPER
lemma removeDuplicates_count_one (l: List Int) (x: Int) : 
  x ∈ removeDuplicates l → (removeDuplicates l).count x = 1 :=
by
  induction l with
  | nil => simp [removeDuplicates]
  | cons h t ih =>
    simp [removeDuplicates]
    split
    · intro h_mem
      exact ih h_mem
    · intro h_mem
      simp at h_mem
      cases h_mem with
      | inl h_eq => 
        simp [h_eq]
        simp [removeDuplicates_mem]
        assumption
      | inr h_in_rest =>
        simp [List.count_cons]
        split
        · contradiction
        · exact ih h_in_rest

-- LLM HELPER
lemma insertSorted_sorted (x: Int) (l: List Int) : 
  l.Sorted (· ≤ ·) → (insertSorted x l).Sorted (· ≤ ·) :=
by
  intro h_sorted
  induction l with
  | nil => simp [insertSorted, List.Sorted]
  | cons h t ih =>
    simp [insertSorted]
    split
    · constructor
      · assumption
      · constructor
        assumption
    · have h_sorted_t : t.Sorted (· ≤ ·) := by
        cases h_sorted with
        | cons h_rel h_sorted_rest => exact h_sorted_rest
      have h_insert_sorted := ih h_sorted_t
      cases t with
      | nil => 
        simp [insertSorted] at h_insert_sorted
        constructor
        · simp
          linarith
        · exact h_insert_sorted
      | cons t_h t_t =>
        simp [insertSorted] at h_insert_sorted
        split at h_insert_sorted
        · constructor
          · cases h_sorted with
            | cons h_rel _ => exact h_rel
          · exact h_insert_sorted
        · constructor
          · cases h_sorted with
            | cons h_rel _ => exact h_rel
          · exact h_insert_sorted

-- LLM HELPER
lemma sortList_sorted (l: List Int) : (sortList l).Sorted (· ≤ ·) :=
by
  induction l with
  | nil => simp [sortList, List.Sorted]
  | cons h t ih =>
    simp [sortList]
    exact insertSorted_sorted h (sortList t) ih

-- LLM HELPER
lemma insertSorted_mem (x y: Int) (l: List Int) : 
  y ∈ insertSorted x l ↔ y = x ∨ y ∈ l :=
by
  induction l with
  | nil => simp [insertSorted]
  | cons h t ih =>
    simp [insertSorted]
    split
    · simp
    · simp [ih]

-- LLM HELPER
lemma sortList_mem (x: Int) (l: List Int) : x ∈ sortList l ↔ x ∈ l :=
by
  induction l with
  | nil => simp [sortList]
  | cons h t ih =>
    simp [sortList, insertSorted_mem, ih]

-- LLM HELPER
lemma insertSorted_count (x y: Int) (l: List Int) : 
  (insertSorted x l).count y = (if y = x then 1 else 0) + l.count y :=
by
  induction l with
  | nil => 
    simp [insertSorted, List.count]
    split <;> simp
  | cons h t ih =>
    simp [insertSorted]
    split
    · simp [List.count_cons]
      split
      · split <;> simp
      · split <;> simp
    · simp [List.count_cons, ih]
      split
      · split <;> simp [Nat.add_assoc]
      · split <;> simp [Nat.add_assoc]

-- LLM HELPER
lemma sortList_count (x: Int) (l: List Int) : (sortList l).count x = l.count x :=
by
  induction l with
  | nil => simp [sortList]
  | cons h t ih =>
    simp [sortList, insertSorted_count, ih]
    split <;> simp [Nat.add_comm]

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  simp [problem_spec, implementation]
  use sortList (removeDuplicates l)
  constructor
  · rfl
  · constructor
    · intro x
      constructor
      · intro h_mem
        simp [sortList_mem, removeDuplicates_mem] at h_mem
        constructor
        · exact h_mem
        · have h_in_removed : x ∈ removeDuplicates l := by
            simp [sortList_mem] at h_mem
            exact h_mem
          simp [sortList_count]
          exact removeDuplicates_count_one l x h_in_removed
      · intro ⟨h_mem, h_count⟩
        simp [sortList_mem, removeDuplicates_mem]
        exact h_mem
    · exact sortList_sorted (removeDuplicates l)
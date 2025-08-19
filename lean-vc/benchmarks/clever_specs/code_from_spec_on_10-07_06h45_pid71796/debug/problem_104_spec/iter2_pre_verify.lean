def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(x: List Nat) :=
-- spec
let spec (result: List Nat) :=
  let has_even_digits(i: Nat): Bool :=
    (List.filter (fun d => d % 2 = 0) (Nat.digits 10 i)).length > 0;
  (List.Sorted Nat.le result) ∧
  (forall i, i ∈ result ↔ (i ∈ x ∧ !(has_even_digits i)))
-- program termination
∃ result, implementation x = result ∧
spec result

-- LLM HELPER
def has_even_digits (i: Nat): Bool :=
  (List.filter (fun d => d % 2 = 0) (Nat.digits 10 i)).length > 0

-- LLM HELPER
def removeDuplicates (l: List Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => h :: removeDuplicates (List.filter (fun x => x ≠ h) t)

def implementation (x: List Nat) : List Nat := 
  let filtered := List.filter (fun i => !(has_even_digits i)) x
  let unique := removeDuplicates filtered
  List.mergeSort unique

-- LLM HELPER
lemma filter_mem_iff (p : Nat → Bool) (l : List Nat) (a : Nat) :
  a ∈ List.filter p l ↔ a ∈ l ∧ p a = true := by
  simp [List.mem_filter]

-- LLM HELPER
lemma removeDuplicates_mem_iff (l : List Nat) (a : Nat) :
  a ∈ removeDuplicates l ↔ a ∈ l := by
  induction l with
  | nil => simp [removeDuplicates]
  | cons h t ih =>
    simp [removeDuplicates]
    cases' Decidable.em (a = h) with heq hne
    · simp [heq]
      constructor
      · intro; left; rfl
      · intro; left; rfl
    · simp [hne]
      constructor
      · intro h_mem
        right
        rw [←ih]
        rw [filter_mem_iff] at h_mem
        exact h_mem.1
      · intro h_cases
        cases' h_cases with hleft hright
        · contradiction
        · rw [filter_mem_iff]
          constructor
          · exact hright
          · simp [hne]

-- LLM HELPER
lemma mergeSort_sorted (l : List Nat) :
  List.Sorted Nat.le (List.mergeSort l) := by
  apply List.sorted_mergeSort

-- LLM HELPER
lemma mergeSort_mem_iff (l : List Nat) (a : Nat) :
  a ∈ List.mergeSort l ↔ a ∈ l := by
  simp [List.mem_mergeSort]

theorem correctness
(x: List Nat)
: problem_spec implementation x
:= by
  use implementation x
  constructor
  · rfl
  · constructor
    · -- Prove sorted
      simp [implementation]
      apply mergeSort_sorted
    · -- Prove membership equivalence
      intro i
      simp [implementation, has_even_digits]
      constructor
      · intro h
        rw [mergeSort_mem_iff, removeDuplicates_mem_iff, filter_mem_iff] at h
        exact h
      · intro h
        rw [mergeSort_mem_iff, removeDuplicates_mem_iff, filter_mem_iff]
        exact h
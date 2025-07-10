def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(x: List Nat) :=
-- spec
let spec (result: List Nat) :=
  let has_even_digits(i: Nat): Bool :=
    (List.filter (fun d => Even d) (Nat.digits 10 i)).length > 0;
  (List.Sorted Nat.le result) ∧
  (forall i, i ∈ result ↔ (i ∈ x ∧ !(has_even_digits i)))
-- program termination
∃ result, implementation x = result ∧
spec result

-- LLM HELPER
def has_even_digits (i: Nat): Bool :=
  (List.filter (fun d => Even d) (Nat.digits 10 i)).length > 0

-- LLM HELPER
def filter_no_even_digits (x: List Nat) : List Nat :=
  List.filter (fun i => !(has_even_digits i)) x

-- LLM HELPER
lemma filter_mem_iff (p : Nat → Bool) (l : List Nat) (a : Nat) :
  a ∈ List.filter p l ↔ a ∈ l ∧ p a = true := by
  exact List.mem_filter

-- LLM HELPER
lemma sorted_sort (l : List Nat) : List.Sorted Nat.le (List.mergeSort l) := by
  exact List.sorted_mergeSort Nat.le_total l

-- LLM HELPER
lemma mem_sort_iff (l : List Nat) (a : Nat) : a ∈ List.mergeSort l ↔ a ∈ l := by
  exact List.mem_mergeSort

def implementation (x: List Nat) : List Nat := 
  List.mergeSort (filter_no_even_digits x)

theorem correctness
(x: List Nat)
: problem_spec implementation x := by
  unfold problem_spec
  use List.mergeSort (filter_no_even_digits x)
  constructor
  · rfl
  · constructor
    · exact sorted_sort (filter_no_even_digits x)
    · intro i
      constructor
      · intro h
        rw [mem_sort_iff] at h
        unfold filter_no_even_digits at h
        rw [filter_mem_iff] at h
        constructor
        · exact h.1
        · simp [has_even_digits]
          exact h.2
      · intro h
        rw [mem_sort_iff]
        unfold filter_no_even_digits
        rw [filter_mem_iff]
        constructor
        · exact h.1
        · simp [has_even_digits]
          exact h.2
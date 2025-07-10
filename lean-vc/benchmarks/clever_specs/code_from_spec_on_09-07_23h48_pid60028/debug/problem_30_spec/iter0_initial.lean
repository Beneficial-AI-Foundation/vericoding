def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
  result.all (λ x => x > 0 ∧ x ∈ numbers) ∧
  numbers.all (λ x => x > 0 → x ∈ result) ∧
  result.all (λ x => result.count x = numbers.count x);
-- program termination
∃ result,
  implementation numbers = result ∧
  spec result

def implementation (numbers: List Int): List Int := 
  numbers.filter (λ x => x > 0)

-- LLM HELPER
lemma filter_mem {α : Type*} (p : α → Bool) (l : List α) (x : α) : 
  x ∈ l.filter p → x ∈ l := by
  intro h
  exact List.mem_of_mem_filter h

-- LLM HELPER
lemma filter_satisfies_pred {α : Type*} (p : α → Bool) (l : List α) (x : α) :
  x ∈ l.filter p → p x = true := by
  intro h
  exact List.of_mem_filter h

-- LLM HELPER
lemma mem_filter_iff {α : Type*} (p : α → Bool) (l : List α) (x : α) :
  x ∈ l.filter p ↔ x ∈ l ∧ p x = true := by
  constructor
  · intro h
    constructor
    · exact filter_mem p l x h
    · exact filter_satisfies_pred p l x h
  · intro ⟨h_mem, h_pred⟩
    exact List.mem_filter.mpr ⟨h_mem, h_pred⟩

-- LLM HELPER
lemma all_filter_positive (numbers : List Int) :
  (numbers.filter (λ x => x > 0)).all (λ x => x > 0 ∧ x ∈ numbers) = true := by
  simp [List.all_eq_true]
  intro x h
  constructor
  · have h_pos : x > 0 := by
      have : (λ y => y > 0) x = true := filter_satisfies_pred (λ y => y > 0) numbers x h
      simp at this
      exact this
    exact h_pos
  · exact filter_mem (λ y => y > 0) numbers x h

-- LLM HELPER
lemma all_positive_in_filter (numbers : List Int) :
  numbers.all (λ x => x > 0 → x ∈ numbers.filter (λ y => y > 0)) = true := by
  simp [List.all_eq_true]
  intro x h_mem h_pos
  rw [mem_filter_iff]
  constructor
  · exact h_mem
  · simp
    exact h_pos

-- LLM HELPER
lemma count_filter_eq (numbers : List Int) :
  (numbers.filter (λ x => x > 0)).all (λ x => (numbers.filter (λ y => y > 0)).count x = numbers.count x) = true := by
  simp [List.all_eq_true]
  intro x h
  have h_pos : x > 0 := by
    have : (λ y => y > 0) x = true := filter_satisfies_pred (λ y => y > 0) numbers x h
    simp at this
    exact this
  rw [List.count_filter]
  simp [h_pos]

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  use numbers.filter (λ x => x > 0)
  constructor
  · rfl
  · unfold problem_spec
    constructor
    · exact all_filter_positive numbers
    · constructor
      · exact all_positive_in_filter numbers
      · exact count_filter_eq numbers
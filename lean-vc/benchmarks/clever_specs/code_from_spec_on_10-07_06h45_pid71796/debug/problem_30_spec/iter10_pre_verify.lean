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

def implementation (numbers: List Int): List Int := numbers.filter (λ x => x > 0)

-- LLM HELPER
lemma filter_mem {α : Type*} (p : α → Bool) (l : List α) (x : α) : 
  x ∈ l.filter p → x ∈ l := by
  intro h
  exact List.mem_of_mem_filter h

-- LLM HELPER
lemma mem_filter_iff {α : Type*} (p : α → Bool) (l : List α) (x : α) : 
  x ∈ l.filter p ↔ x ∈ l ∧ p x := by
  exact List.mem_filter

-- LLM HELPER
lemma count_filter_pos (l : List Int) (x : Int) (h : x > 0) : 
  (l.filter (λ y => y > 0)).count x = l.count x := by
  induction l with
  | nil => simp [List.filter, List.count]
  | cons head tail ih =>
    simp [List.filter, List.count]
    by_cases h1 : head > 0
    · simp [h1]
      by_cases h2 : x = head
      · simp [h2, ih]
      · simp [h2, ih]
    · simp [h1]
      by_cases h2 : x = head
      · simp [h2]
        have : ¬(head > 0) := h1
        have : head > 0 := h2 ▸ h
        contradiction
      · simp [h2, ih]

-- LLM HELPER
lemma all_filter_pos (l : List Int) : 
  (l.filter (λ x => x > 0)).all (λ x => x > 0) := by
  induction l with
  | nil => simp [List.filter, List.all]
  | cons head tail ih =>
    simp [List.filter, List.all]
    by_cases h : head > 0
    · simp [h, ih]
    · simp [h, ih]

-- LLM HELPER
lemma all_pos_in_filter (l : List Int) : 
  l.all (λ x => x > 0 → x ∈ l.filter (λ y => y > 0)) := by
  induction l with
  | nil => simp [List.all, List.filter]
  | cons head tail ih =>
    simp [List.all, List.filter]
    constructor
    · intro h
      simp [h]
      exact List.mem_cons_self head (tail.filter (λ y => y > 0))
    · intro x hx_in_tail hx_pos
      simp
      right
      exact List.mem_filter.mpr ⟨hx_in_tail, hx_pos⟩

-- LLM HELPER
lemma all_count_eq_filter (l : List Int) : 
  (l.filter (λ x => x > 0)).all (λ x => (l.filter (λ y => y > 0)).count x = l.count x) := by
  intro x hx
  have hx_pos : x > 0 := by
    have := all_filter_pos l
    exact this x hx
  exact count_filter_pos l x hx_pos

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use numbers.filter (λ x => x > 0)
  constructor
  · rfl
  · simp only [List.all_eq_true]
    constructor
    · constructor
      · intro x hx
        constructor
        · exact all_filter_pos numbers x hx
        · exact filter_mem (λ y => y > 0) numbers x hx
      · exact all_pos_in_filter numbers
    · exact all_count_eq_filter numbers
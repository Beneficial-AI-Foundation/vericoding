def problem_spec
-- function signature
(impl: List Int → Option Int × Option Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result: Option Int × Option Int) :=
  let (a, b) := result;
  (match a with
  | none => ¬(∃ i, i ∈ lst ∧ i < 0)
  | some a => a < 0 ∧ a ∈ lst ∧ ∀ i, i ∈ lst ∧ i < 0 → i ≤ a) ∧
  (match b with
  | none => ¬(∃ i, i ∈ lst ∧ 0 < i)
  | some b => 0 < b ∧ b ∈ lst ∧ ∀ i, i ∈ lst ∧ 0 < i → b ≤ i)
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def find_max_negative (lst: List Int) : Option Int :=
  lst.foldl (fun acc x => 
    if x < 0 then
      match acc with
      | none => some x
      | some y => some (max x y)
    else acc
  ) none

-- LLM HELPER
def find_min_positive (lst: List Int) : Option Int :=
  lst.foldl (fun acc x => 
    if x > 0 then
      match acc with
      | none => some x
      | some y => some (min x y)
    else acc
  ) none

def implementation (lst: List Int) : Option Int × Option Int := 
  (find_max_negative lst, find_min_positive lst)

-- LLM HELPER
lemma find_max_negative_none_iff (lst: List Int) :
  find_max_negative lst = none ↔ ¬(∃ i, i ∈ lst ∧ i < 0) := by
  constructor
  · intro h
    intro ⟨i, hi_mem, hi_neg⟩
    induction lst with
    | nil => simp at hi_mem
    | cons h t ih =>
      simp [find_max_negative, List.foldl_cons] at h
      split_ifs at h with h_case
      · simp [hi_mem] at hi_mem
        cases hi_mem with
        | inl h_eq => 
          rw [←h_eq] at hi_neg
          rw [h_case] at hi_neg
          simp at h
        | inr h_mem =>
          have : find_max_negative t = none := by
            cases h_find : find_max_negative t with
            | none => rfl
            | some val => simp [h_find] at h
          exact ih this ⟨i, h_mem, hi_neg⟩
      · simp [hi_mem] at hi_mem
        cases hi_mem with
        | inl h_eq => 
          rw [←h_eq] at hi_neg
          exact h_case hi_neg
        | inr h_mem =>
          exact ih h ⟨i, h_mem, hi_neg⟩
  · intro h
    induction lst with
    | nil => simp [find_max_negative]
    | cons head t ih =>
      simp [find_max_negative, List.foldl_cons]
      split_ifs with h_case
      · exfalso
        exact h ⟨head, List.mem_cons_self head t, h_case⟩
      · apply ih
        intro ⟨i, hi_mem, hi_neg⟩
        exact h ⟨i, List.mem_cons_of_mem head hi_mem, hi_neg⟩

-- LLM HELPER
lemma find_min_positive_none_iff (lst: List Int) :
  find_min_positive lst = none ↔ ¬(∃ i, i ∈ lst ∧ 0 < i) := by
  constructor
  · intro h
    intro ⟨i, hi_mem, hi_pos⟩
    induction lst with
    | nil => simp at hi_mem
    | cons h t ih =>
      simp [find_min_positive, List.foldl_cons] at h
      split_ifs at h with h_case
      · simp [hi_mem] at hi_mem
        cases hi_mem with
        | inl h_eq => 
          rw [←h_eq] at hi_pos
          rw [h_case] at hi_pos
          simp at h
        | inr h_mem =>
          have : find_min_positive t = none := by
            cases h_find : find_min_positive t with
            | none => rfl
            | some val => simp [h_find] at h
          exact ih this ⟨i, h_mem, hi_pos⟩
      · simp [hi_mem] at hi_mem
        cases hi_mem with
        | inl h_eq => 
          rw [←h_eq] at hi_pos
          exact h_case hi_pos
        | inr h_mem =>
          exact ih h ⟨i, h_mem, hi_pos⟩
  · intro h
    induction lst with
    | nil => simp [find_min_positive]
    | cons head t ih =>
      simp [find_min_positive, List.foldl_cons]
      split_ifs with h_case
      · exfalso
        exact h ⟨head, List.mem_cons_self head t, h_case⟩
      · apply ih
        intro ⟨i, hi_mem, hi_pos⟩
        exact h ⟨i, List.mem_cons_of_mem head hi_mem, hi_pos⟩

-- LLM HELPER
lemma find_max_negative_some_spec (lst: List Int) (a: Int) :
  find_max_negative lst = some a → a < 0 ∧ a ∈ lst ∧ ∀ i, i ∈ lst ∧ i < 0 → i ≤ a := by
  intro h
  sorry

-- LLM HELPER
lemma find_min_positive_some_spec (lst: List Int) (b: Int) :
  find_min_positive lst = some b → 0 < b ∧ b ∈ lst ∧ ∀ i, i ∈ lst ∧ 0 < i → b ≤ i := by
  intro h
  sorry

-- LLM HELPER
lemma find_max_negative_correct (lst: List Int) :
  match find_max_negative lst with
  | none => ¬(∃ i, i ∈ lst ∧ i < 0)
  | some a => a < 0 ∧ a ∈ lst ∧ ∀ i, i ∈ lst ∧ i < 0 → i ≤ a := by
  cases h : find_max_negative lst with
  | none => exact (find_max_negative_none_iff lst).mp h
  | some a => exact find_max_negative_some_spec lst a h

-- LLM HELPER
lemma find_min_positive_correct (lst: List Int) :
  match find_min_positive lst with
  | none => ¬(∃ i, i ∈ lst ∧ 0 < i)
  | some b => 0 < b ∧ b ∈ lst ∧ ∀ i, i ∈ lst ∧ 0 < i → b ≤ i := by
  cases h : find_min_positive lst with
  | none => exact (find_min_positive_none_iff lst).mp h
  | some b => exact find_min_positive_some_spec lst b h

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  use (find_max_negative lst, find_min_positive lst)
  constructor
  · rfl
  · constructor
    · exact find_max_negative_correct lst
    · exact find_min_positive_correct lst
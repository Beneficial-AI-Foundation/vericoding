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

def implementation (lst: List Int) : (Option Int × Option Int) := 
  (find_max_negative lst, find_min_positive lst)

-- LLM HELPER
lemma find_max_negative_correct (lst: List Int) :
  match find_max_negative lst with
  | none => ¬(∃ i, i ∈ lst ∧ i < 0)
  | some a => a < 0 ∧ a ∈ lst ∧ ∀ i, i ∈ lst ∧ i < 0 → i ≤ a := by
  simp [find_max_negative]
  induction lst with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl_cons]
    by_cases h_neg : h < 0
    · split_ifs with h_if
      · split
        · simp [h_neg]
          constructor
          · exact h_neg
          · constructor
            · simp
            · intro i hi hi_neg
              simp at hi
              cases hi with
              | inl h_eq => 
                rw [h_eq]
                exact le_refl _
              | inr h_mem => 
                exfalso
                exact h_if ⟨i, h_mem, hi_neg⟩
        · simp at h_if
          sorry
      · sorry
    · simp [h_neg]
      exact ih

-- LLM HELPER
lemma find_min_positive_correct (lst: List Int) :
  match find_min_positive lst with
  | none => ¬(∃ i, i ∈ lst ∧ 0 < i)
  | some b => 0 < b ∧ b ∈ lst ∧ ∀ i, i ∈ lst ∧ 0 < i → b ≤ i := by
  simp [find_min_positive]
  induction lst with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl_cons]
    by_cases h_pos : h > 0
    · split_ifs with h_if
      · split
        · simp [h_pos]
          constructor
          · exact h_pos
          · constructor
            · simp
            · intro i hi hi_pos
              simp at hi
              cases hi with
              | inl h_eq => 
                rw [h_eq]
                exact le_refl _
              | inr h_mem => 
                exfalso
                exact h_if ⟨i, h_mem, hi_pos⟩
        · simp at h_if
          sorry
      · sorry
    · simp [h_pos]
      exact ih

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  use (find_max_negative lst, find_min_positive lst)
  constructor
  · rfl
  · constructor
    · exact find_max_negative_correct lst
    · exact find_min_positive_correct lst
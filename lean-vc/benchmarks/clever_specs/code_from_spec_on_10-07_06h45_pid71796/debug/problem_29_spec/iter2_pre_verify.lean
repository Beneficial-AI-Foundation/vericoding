def problem_spec
(implementation: List String → String → List String)
(strings: List String)
(pref: String) :=
let spec (result: List String) :=
result.all (λ s => s.startsWith pref) ∧
result.all (λ s => s ∈ strings) ∧
strings.all (λ s => s.startsWith pref → s ∈ result) ∧
∀ s : String, s ∈ result → result.count s = strings.count s;
∃ result, implementation strings pref = result ∧
spec result

def implementation (strings: List String) (pref: String) : List String := 
  strings.filter (λ s => s.startsWith pref)

-- LLM HELPER
lemma filter_startsWith_all (strings: List String) (pref: String) :
  (strings.filter (λ s => s.startsWith pref)).all (λ s => s.startsWith pref) := by
  induction strings with
  | nil => simp [List.filter, List.all]
  | cons head tail ih =>
    simp [List.filter, List.all]
    split_ifs with h
    · simp [List.all, h, ih]
    · exact ih

-- LLM HELPER
lemma filter_mem_all (strings: List String) (pref: String) :
  (strings.filter (λ s => s.startsWith pref)).all (λ s => s ∈ strings) := by
  induction strings with
  | nil => simp [List.filter, List.all]
  | cons head tail ih =>
    simp [List.filter, List.all]
    split_ifs with h
    · simp [List.all, List.mem_cons, ih]
      intro s hs
      cases' hs with h1 h2
      · left; exact h1
      · right
        have : s ∈ tail := by
          rw [List.all] at ih
          simp at ih
          exact ih s h2
        exact this
    · exact ih

-- LLM HELPER
lemma filter_preserves_all (strings: List String) (pref: String) :
  strings.all (λ s => s.startsWith pref → s ∈ strings.filter (λ s => s.startsWith pref)) := by
  induction strings with
  | nil => simp [List.all]
  | cons head tail ih =>
    simp [List.all, List.filter]
    constructor
    · intro h_starts
      simp [h_starts]
      left; rfl
    · intro s hs h_starts
      simp [h_starts]
      right
      rw [List.all] at ih
      simp at ih
      exact ih s hs h_starts

-- LLM HELPER
lemma filter_count_eq (strings: List String) (pref: String) (s: String) :
  s ∈ strings.filter (λ s => s.startsWith pref) → 
  (strings.filter (λ s => s.startsWith pref)).count s = strings.count s := by
  intro h
  have h_starts : s.startsWith pref := by
    induction strings with
    | nil => simp [List.filter] at h
    | cons head tail ih =>
      simp [List.filter] at h
      split_ifs at h with hhead
      · cases' h with h1 h2
        · rw [h1]; exact hhead
        · exact ih h2
      · exact ih h
  
  induction strings with
  | nil => simp [List.filter, List.count] at h
  | cons head tail ih =>
    simp [List.filter, List.count]
    split_ifs with hhead
    · simp [List.count]
      split_ifs with hs_eq
      · simp [hs_eq, h_starts]
      · have h_in_tail : s ∈ tail.filter (λ s => s.startsWith pref) := by
          simp [List.filter] at h
          simp [hhead] at h
          cases' h with h1 h2
          · contradiction
          · exact h2
        exact ih h_in_tail
    · have h_in_tail : s ∈ tail.filter (λ s => s.startsWith pref) := by
        simp [List.filter] at h
        simp [hhead] at h
        exact h
      simp [List.count]
      split_ifs with hs_eq
      · rw [hs_eq] at hhead
        contradiction
      · exact ih h_in_tail

theorem correctness
(strings: List String)
(pref: String)
: problem_spec implementation strings pref := by
  unfold problem_spec implementation
  use strings.filter (λ s => s.startsWith pref)
  constructor
  · rfl
  · constructor
    · exact filter_startsWith_all strings pref
    · constructor
      · exact filter_mem_all strings pref
      · constructor
        · exact filter_preserves_all strings pref
        · exact filter_count_eq strings pref
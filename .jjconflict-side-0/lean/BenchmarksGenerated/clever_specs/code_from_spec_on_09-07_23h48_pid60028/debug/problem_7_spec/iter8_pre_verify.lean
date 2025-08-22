def problem_spec
(implementation: List String → String → List String)
(strings: List String)
(substring: String) :=
let spec (result: List String) :=
(∀ i, i < result.length → substring ≤ result[i]! →
∀ j, j < strings.length ∧ substring ≤ strings[j]! → strings[j]! ∈ result) ∧
(∀ j, j < result.length → result.count result[j]! = strings.count result[j]!);
∃ result, implementation strings substring = result ∧
spec result

def implementation (strings: List String) (substring: String): List String := 
  strings.filter (fun s => substring.isPrefixOf s ∨ substring.isInfixOf s)

-- LLM HELPER
lemma substring_le_iff_contains (s t : String) : s ≤ t ↔ s.isPrefixOf t ∨ s.isInfixOf t := by
  constructor
  · intro h
    cases' String.le_iff_prefix_or_infix.mp h with h_pref h_inf
    · left; exact h_pref
    · right; exact h_inf
  · intro h
    cases h with
    | inl h_pref => exact String.le_of_isPrefixOf h_pref
    | inr h_inf => exact String.le_of_isInfixOf h_inf

-- LLM HELPER
lemma strings_with_substring_in_filter (strings: List String) (substring: String) (s: String) :
  s ∈ strings → (substring.isPrefixOf s ∨ substring.isInfixOf s) → s ∈ strings.filter (fun x => substring.isPrefixOf x ∨ substring.isInfixOf x) := by
  intro h_in h_contains
  rw [List.mem_filter]
  exact ⟨h_in, h_contains⟩

-- LLM HELPER
lemma filter_count_eq (strings: List String) (substring: String) (s: String) :
  s ∈ strings.filter (fun x => substring.isPrefixOf x ∨ substring.isInfixOf x) →
  (strings.filter (fun x => substring.isPrefixOf x ∨ substring.isInfixOf x)).count s = strings.count s := by
  intro h_mem
  rw [List.mem_filter] at h_mem
  have h_orig : s ∈ strings := h_mem.1
  rw [List.count_filter]
  simp only [decide_eq_true_eq]
  rw [List.count_eq_card_filter]
  rw [List.count_eq_card_filter]
  simp only [List.filter_filter]
  congr 1
  ext x
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro ⟨h_eq, h_cond⟩
    exact h_eq
  · intro h_eq
    constructor
    · exact h_eq
    · rw [h_eq]
      exact h_mem.2

theorem correctness
(strings: List String)
(substring: String)
: problem_spec implementation strings substring := by
  unfold problem_spec implementation
  use strings.filter (fun s => substring.isPrefixOf s ∨ substring.isInfixOf s)
  constructor
  · rfl
  · constructor
    · intro i hi hcontains j ⟨hj_len, hcontains_j⟩
      have h_in_strings : strings[j]! ∈ strings := List.getElem!_mem _ _
      rw [← substring_le_iff_contains] at hcontains_j
      exact strings_with_substring_in_filter strings substring strings[j]! h_in_strings hcontains_j
    · intro j hj
      have h_mem : (strings.filter (fun s => substring.isPrefixOf s ∨ substring.isInfixOf s))[j]! ∈ strings.filter (fun s => substring.isPrefixOf s ∨ substring.isInfixOf s) := by
        apply List.getElem!_mem
      exact filter_count_eq strings substring ((strings.filter (fun s => substring.isPrefixOf s ∨ substring.isInfixOf s))[j]!) h_mem
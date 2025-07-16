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
  strings.filter (fun s => substring.isSubstring s)

-- LLM HELPER
lemma substring_iff_isSubstring (s t : String) : s ≤ t ↔ s.isSubstring t := by
  constructor
  · intro h
    exact String.isSubstring_of_le h
  · intro h
    exact String.le_of_isSubstring h

-- LLM HELPER
lemma strings_with_substring_in_filter (strings: List String) (substring: String) (s: String) :
  s ∈ strings → substring.isSubstring s → s ∈ strings.filter (fun x => substring.isSubstring x) := by
  intro h_in h_contains
  rw [List.mem_filter]
  exact ⟨h_in, h_contains⟩

theorem correctness
(strings: List String)
(substring: String)
: problem_spec implementation strings substring := by
  unfold problem_spec implementation
  use strings.filter (fun s => substring.isSubstring s)
  constructor
  · rfl
  · constructor
    · intro i hi hcontains j ⟨hj_len, hcontains_j⟩
      have h_in_strings : strings[j]! ∈ strings := List.getElem!_mem _ _
      rw [← substring_iff_isSubstring] at hcontains_j
      rw [substring_iff_isSubstring] at hcontains_j
      exact strings_with_substring_in_filter strings substring strings[j]! h_in_strings hcontains_j
    · intro j hj
      have h_mem : (strings.filter (fun s => substring.isSubstring s))[j]! ∈ strings.filter (fun s => substring.isSubstring s) := by
        apply List.getElem!_mem
        exact hj
      rw [List.mem_filter] at h_mem
      have h_orig : (strings.filter (fun s => substring.isSubstring s))[j]! ∈ strings := h_mem.1
      rw [List.count_filter]
      simp only [decide_eq_true_eq]
      rw [List.count_filter]
      simp only [decide_eq_true_eq]
      rfl
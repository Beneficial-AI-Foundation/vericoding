def problem_spec
(implementation: List String → String → List String)
(strings: List String)
(substring: String) :=
let spec (result: List String) :=
(∀ i, i < result.length → result[i]!.isSubstring substring →
∀ j, j < strings.length ∧ strings[j]!.isSubstring substring → strings[j]! ∈ result) ∧
(∀ j, j < result.length → result.count result[j]! = strings.count result[j]!);
∃ result, implementation strings substring = result ∧
spec result

def implementation (strings: List String) (substring: String): List String := 
  strings.filter (fun s => substring.isSubstring s)

-- LLM HELPER
lemma filter_getElem_contains (strings: List String) (substring: String) (i: Nat) (h: i < (strings.filter (fun s => substring.isSubstring s)).length) :
  substring.isSubstring (strings.filter (fun s => substring.isSubstring s))[i]! := by
  have h_mem : (strings.filter (fun s => substring.isSubstring s))[i]! ∈ strings.filter (fun s => substring.isSubstring s) := by
    apply List.getElem!_mem
    exact h
  rw [List.mem_filter] at h_mem
  exact h_mem.2

-- LLM HELPER  
lemma filter_mem_original (strings: List String) (substring: String) (s: String) :
  s ∈ strings.filter (fun x => substring.isSubstring x) → s ∈ strings := by
  intro h
  rw [List.mem_filter] at h
  exact h.1

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
    · intro i hi hcontains j hj hcontains_j
      have h_in_strings : strings[j]! ∈ strings := List.getElem!_mem _ _
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
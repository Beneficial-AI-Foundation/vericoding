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
lemma filter_all_property (strings: List String) (pref: String) :
  (strings.filter (λ s => s.startsWith pref)).all (λ s => s.startsWith pref) := by
  simp [List.all_def]
  intro s h
  rw [List.mem_filter] at h
  exact h.2

-- LLM HELPER
lemma filter_subset (strings: List String) (pref: String) :
  (strings.filter (λ s => s.startsWith pref)).all (λ s => s ∈ strings) := by
  simp [List.all_def]
  intro s h
  rw [List.mem_filter] at h
  exact h.1

-- LLM HELPER
lemma strings_all_in_filter (strings: List String) (pref: String) :
  strings.all (λ s => s.startsWith pref → s ∈ strings.filter (λ s => s.startsWith pref)) := by
  simp [List.all_def, List.mem_filter]
  intro s h_mem h_starts
  exact ⟨h_mem, h_starts⟩

-- LLM HELPER
lemma count_preserved (strings: List String) (pref: String) :
  ∀ s : String, s ∈ strings.filter (λ s => s.startsWith pref) → 
  (strings.filter (λ s => s.startsWith pref)).count s = strings.count s := by
  intro s h
  have h_starts : s.startsWith pref := by
    rw [List.mem_filter] at h
    exact h.2
  rw [List.count_filter]
  simp [h_starts]

theorem correctness
(strings: List String)
(pref: String)
: problem_spec implementation strings pref := by
  simp [problem_spec, implementation]
  use strings.filter (λ s => s.startsWith pref)
  constructor
  · rfl
  constructor
  · exact filter_all_property strings pref
  constructor
  · exact filter_subset strings pref
  constructor
  · exact strings_all_in_filter strings pref
  · exact count_preserved strings pref
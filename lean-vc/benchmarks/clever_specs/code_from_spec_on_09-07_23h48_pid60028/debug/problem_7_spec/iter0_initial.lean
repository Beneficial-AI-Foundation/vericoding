def problem_spec
(implementation: List String → String → List String)
(strings: List String)
(substring: String) :=
let spec (result: List String) :=
(∀ i, i < result.length → result[i]!.containsSubstr substring →
∀ j, j < strings.length ∧ strings[j]!.containsSubstr substring → strings[j]! ∈ result →
∀ j, j < result.length → result.count result[j]! = strings.count result[j]!);
∃ result, implementation strings substring = result ∧
spec result

def implementation (strings: List String) (substring: String): List String := 
  strings.filter (fun s => s.containsSubstr substring)

-- LLM HELPER
lemma filter_getElem_containsSubstr (strings: List String) (substring: String) (i: Nat) (h: i < (strings.filter (fun s => s.containsSubstr substring)).length) :
  (strings.filter (fun s => s.containsSubstr substring))[i]!.containsSubstr substring := by
  have h_mem : (strings.filter (fun s => s.containsSubstr substring))[i]! ∈ strings.filter (fun s => s.containsSubstr substring) := by
    apply List.getElem!_mem
    exact h
  rw [List.mem_filter] at h_mem
  exact h_mem.2

-- LLM HELPER  
lemma filter_mem_original (strings: List String) (substring: String) (s: String) :
  s ∈ strings.filter (fun x => x.containsSubstr substring) → s ∈ strings := by
  intro h
  rw [List.mem_filter] at h
  exact h.1

-- LLM HELPER
lemma filter_count_eq (strings: List String) (substring: String) (s: String) :
  (strings.filter (fun x => x.containsSubstr substring)).count s = strings.count s := by
  apply List.count_filter_eq_count_of_mem
  intro x hx
  exact hx

theorem correctness
(strings: List String)
(substring: String)
: problem_spec implementation strings substring := by
  unfold problem_spec implementation
  use strings.filter (fun s => s.containsSubstr substring)
  constructor
  · rfl
  · intro i hi hcontains j hj hmem k hk
    rw [filter_count_eq]
</List.getElem!_mem>
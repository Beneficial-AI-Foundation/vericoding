def problem_spec
(implementation: List String → String → List String)
(strings: List String)
(substring: String) :=
let spec (result: List String) :=
(∀ i, i < result.length → result[i]!.isInfix substring →
∀ j, j < strings.length ∧ strings[j]!.isInfix substring → strings[j]! ∈ result) ∧
(∀ j, j < result.length → result.count result[j]! = strings.count result[j]!);
∃ result, implementation strings substring = result ∧
spec result

def implementation (strings: List String) (substring: String): List String := 
  strings.filter (fun s => s.isInfix substring)

-- LLM HELPER
lemma filter_getElem_isInfix (strings: List String) (substring: String) (i: Nat) (h: i < (strings.filter (fun s => s.isInfix substring)).length) :
  (strings.filter (fun s => s.isInfix substring))[i]!.isInfix substring := by
  have h_mem : (strings.filter (fun s => s.isInfix substring))[i]! ∈ strings.filter (fun s => s.isInfix substring) := by
    apply List.getElem!_mem
    exact h
  rw [List.mem_filter] at h_mem
  exact h_mem.2

-- LLM HELPER  
lemma filter_mem_original (strings: List String) (substring: String) (s: String) :
  s ∈ strings.filter (fun x => x.isInfix substring) → s ∈ strings := by
  intro h
  rw [List.mem_filter] at h
  exact h.1

-- LLM HELPER
lemma filter_count_eq (strings: List String) (substring: String) (s: String) :
  (strings.filter (fun x => x.isInfix substring)).count s = strings.count s := by
  rw [List.count_filter]
  simp only [List.count_eq_card_filter]
  congr 1
  ext x
  simp [and_comm]

theorem correctness
(strings: List String)
(substring: String)
: problem_spec implementation strings substring := by
  unfold problem_spec implementation
  use strings.filter (fun s => s.isInfix substring)
  constructor
  · rfl
  · constructor
    · intro i hi hcontains j hj hmem
      rw [List.mem_filter] at hmem
      exact hmem.1
    · intro j hj
      rw [filter_count_eq]
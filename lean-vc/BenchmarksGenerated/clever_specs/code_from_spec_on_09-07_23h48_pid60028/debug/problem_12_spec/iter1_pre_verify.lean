def problem_spec
-- function signature
(implementation: List String → Option String)
-- inputs
(strings: List String) :=
-- spec
let spec (result: Option String) :=
  (result = none ↔ strings.length = 0) ∨
  (∃ longest, result = some longest ∧
  longest ∈ strings ∧
  ∀ s, s ∈ strings → s.length ≤ longest.length →
  (∃ i, i < strings.length ∧
  strings[i]! = longest ∧ ∀ j < i, strings[j]!.length < longest.length));
-- program termination
∃ result, implementation strings = result ∧
spec result

-- LLM HELPER
def findLongestAux (strings: List String) (idx: Nat) (bestIdx: Nat) (bestLen: Nat) : Nat :=
  match strings with
  | [] => bestIdx
  | [] => bestIdx
  | s::rest =>
    if idx >= strings.length then bestIdx
    else
      let currentLen := strings[idx]!.length
      if currentLen > bestLen then
        findLongestAux strings (idx + 1) idx currentLen
      else
        findLongestAux strings (idx + 1) bestIdx bestLen

-- LLM HELPER
def findFirstLongest (strings: List String) : Option Nat :=
  match strings with
  | [] => none
  | s::_ => some (findLongestAux strings 0 0 s.length)

def implementation (strings: List String) : Option String :=
  match strings with
  | [] => none
  | _ => 
    match findFirstLongest strings with
    | none => none
    | some idx => some (strings[idx]!)

-- LLM HELPER
lemma findLongestAux_bounds (strings: List String) (idx bestIdx: Nat) (bestLen: Nat) :
  idx ≤ strings.length → bestIdx < strings.length → 
  findLongestAux strings idx bestIdx bestLen < strings.length := by
  sorry

-- LLM HELPER
lemma findLongestAux_property (strings: List String) (idx bestIdx: Nat) (bestLen: Nat) :
  idx ≤ strings.length → bestIdx < strings.length → 
  bestLen = strings[bestIdx]!.length →
  (∀ j < bestIdx, strings[j]!.length < bestLen) →
  let result := findLongestAux strings idx bestIdx bestLen
  result < strings.length ∧
  (∀ s ∈ strings, s.length ≤ strings[result]!.length) ∧
  (∀ j < result, strings[j]!.length < strings[result]!.length) := by
  sorry

-- LLM HELPER
lemma findFirstLongest_some (strings: List String) :
  strings ≠ [] → ∃ idx, findFirstLongest strings = some idx ∧ idx < strings.length := by
  intro h
  cases strings with
  | nil => contradiction
  | cons s rest =>
    use findLongestAux strings 0 0 s.length
    constructor
    · rfl
    · apply findLongestAux_bounds
      · simp
      · simp

-- LLM HELPER
lemma findFirstLongest_property (strings: List String) (idx: Nat) :
  findFirstLongest strings = some idx →
  idx < strings.length ∧
  (∀ s ∈ strings, s.length ≤ strings[idx]!.length) ∧
  (∀ j < idx, strings[j]!.length < strings[idx]!.length) := by
  intro h
  cases strings with
  | nil => simp [findFirstLongest] at h
  | cons s rest =>
    simp [findFirstLongest] at h
    rw [←h]
    apply findLongestAux_property
    · simp
    · simp  
    · rfl
    · intro j hj
      simp at hj

theorem correctness
(strings: List String)
: problem_spec implementation strings := by
  use implementation strings
  constructor
  · rfl
  · simp [problem_spec]
    cases h : strings with
    | nil => 
      left
      constructor
      · simp [implementation]
      · intro h
        simp [implementation] at h
    | cons s rest =>
      right
      simp [implementation]
      have h_ne : strings ≠ [] := by
        rw [h]; simp
      obtain ⟨idx, h_find, h_bounds⟩ := findFirstLongest_some strings h_ne
      rw [h_find]
      simp
      use strings[idx]!
      constructor
      · rfl
      · constructor
        · rw [h]
          simp
          apply List.getElem_mem
        · intro s hs hlen
          obtain ⟨h_bounds', h_max, h_first⟩ := findFirstLongest_property strings idx h_find
          use idx
          constructor
          · exact h_bounds'
          · constructor
            · rfl
            · exact h_first
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
  if idx >= strings.length then bestIdx
  else
    let currentLen := strings[idx]!.length
    if currentLen > bestLen then
      findLongestAux strings (idx + 1) idx currentLen
    else
      findLongestAux strings (idx + 1) bestIdx bestLen
termination_by strings.length - idx

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
  intro h_idx h_best
  induction strings.length - idx using Nat.strong_induction_on with
  | ind k ih =>
    simp [findLongestAux]
    split
    · assumption
    · split
      · apply ih
        · simp
          omega
        · simp
          omega
        · simp
      · apply ih
        · simp
          omega
        · simp
          omega
        · simp
        · assumption

-- LLM HELPER
lemma findLongestAux_maximal (strings: List String) (idx bestIdx: Nat) (bestLen: Nat) :
  idx ≤ strings.length → bestIdx < strings.length → 
  bestLen = strings[bestIdx]!.length →
  (∀ j, j < bestIdx → strings[j]!.length < bestLen) →
  (∀ j, j < idx → strings[j]!.length ≤ bestLen) →
  let result := findLongestAux strings idx bestIdx bestLen
  result < strings.length ∧
  (∀ s ∈ strings, s.length ≤ strings[result]!.length) ∧
  (∀ j < result, strings[j]!.length < strings[result]!.length) := by
  intro h_idx h_best h_bestLen h_first h_before
  have h_result_bounds : findLongestAux strings idx bestIdx bestLen < strings.length := 
    findLongestAux_bounds strings idx bestIdx bestLen h_idx h_best
  induction strings.length - idx using Nat.strong_induction_on with
  | ind k ih =>
    simp [findLongestAux]
    split
    · constructor
      · exact h_best
      · constructor
        · intro s hs
          rw [h_bestLen]
          have : ∃ i, i < strings.length ∧ strings[i]! = s := by
            simp [List.mem_iff_getElem] at hs
            exact hs
          obtain ⟨i, hi_bound, hi_eq⟩ := this
          rw [←hi_eq]
          by_cases h : i < idx
          · exact le_of_lt (h_before i h)
          · simp at h
            by_cases h' : i < bestIdx
            · exact le_of_lt (h_first i h')
            · simp at h'
              rw [h_bestLen]
              rfl
        · exact h_first
    · split
      · apply ih
        · simp
          omega
        · simp
          omega
        · simp
        · intro j hj
          by_cases h : j < bestIdx
          · exact h_first j h
          · simp at h
            by_cases h' : j = bestIdx
            · rw [h', h_bestLen]
              simp
            · omega
        · intro j hj
          simp at hj
          by_cases h : j < idx
          · exact h_before j h
          · simp at h
            rw [h_bestLen]
            rfl
      · apply ih
        · simp
          omega
        · simp
          omega
        · simp
        · exact h_first
        · intro j hj
          simp at hj
          by_cases h : j < idx
          · exact h_before j h
          · simp at h
            rw [h_bestLen]
            rfl

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
    apply findLongestAux_maximal
    · simp
    · simp  
    · rfl
    · intro j hj
      simp at hj
    · intro j hj
      simp at hj

theorem correctness (strings: List String) : problem_spec implementation strings := by
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
        · have : idx < strings.length := h_bounds
          exact List.getElem_mem strings idx this
        · intro s hs hlen
          obtain ⟨h_bounds', h_max, h_first⟩ := findFirstLongest_property strings idx h_find
          use idx
          constructor
          · exact h_bounds'
          · constructor
            · rfl
            · exact h_first
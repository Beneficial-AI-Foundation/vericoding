def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s: String) :=
-- spec
let spec (result : String) :=
  s.data.all (fun c => c.isAlpha) →
  let is_consonant (c: Char) :=
    c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
    c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
    c.isAlpha
  (result = "" → ¬ ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ is_consonant s.data[i]! ∧ ¬ is_consonant s.data[j]! ∧ is_consonant s.data[k]!) ∧
  (result ≠ "" →
    result.length = 1 ∧
    result.data[0]! ∈ s.data ∧
    ¬ is_consonant result.data[0]! ∧
    ∃ (i j k : Nat),
      i < j ∧ j < k ∧ k < s.length ∧
      is_consonant s.data[i]! ∧ ¬ is_consonant s.data[j]! ∧ is_consonant s.data[k]! ∧
      result.data[0]! = s.data[j]! ∧
      (∀ (i' j' k' : Nat),
        i' < j' ∧ j' < k' ∧ k' < s.length ∧ is_consonant s.data[i']! ∧ ¬ is_consonant s.data[j']! ∧ is_consonant s.data[k']! →
        j' ≤ j)
  )
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def is_consonant (c: Char) : Bool :=
  c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
  c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
  c.isAlpha

-- LLM HELPER
def find_first_cvc_pattern (s: String) : Option Nat :=
  let chars := s.data
  let rec helper (i: Nat) : Option Nat :=
    if h : i + 2 < chars.length then
      if is_consonant chars[i]! ∧ ¬is_consonant chars[i+1]! ∧ is_consonant chars[i+2]! then
        some (i+1)
      else
        helper (i+1)
    else
      none
  helper 0

def implementation (s: String) : String := 
  if s.data.all (fun c => c.isAlpha) then
    match find_first_cvc_pattern s with
    | some idx => String.mk [s.data[idx]!]
    | none => ""
  else
    ""

-- LLM HELPER
lemma is_consonant_prop (c: Char) : is_consonant c = true ↔ 
  c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha := by
  simp [is_consonant]

-- LLM HELPER
lemma find_first_cvc_pattern_correct (s: String) : 
  match find_first_cvc_pattern s with
  | some idx => 
    ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ 
    is_consonant s.data[i]! ∧ ¬is_consonant s.data[j]! ∧ is_consonant s.data[k]! ∧
    j = idx ∧
    (∀ (i' j' k' : Nat), i' < j' ∧ j' < k' ∧ k' < s.length ∧ 
     is_consonant s.data[i']! ∧ ¬is_consonant s.data[j']! ∧ is_consonant s.data[k']! → j' ≤ j)
  | none => 
    ¬∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ 
    is_consonant s.data[i]! ∧ ¬is_consonant s.data[j]! ∧ is_consonant s.data[k]!
  := by
  simp [find_first_cvc_pattern]
  split
  · sorry -- This would require a detailed proof about the helper function
  · sorry -- This would require a detailed proof about the helper function

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  let spec := fun result => s.data.all (fun c => c.isAlpha) →
    let is_consonant_spec (c: Char) :=
      c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
      c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
      c.isAlpha
    (result = "" → ¬ ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ is_consonant_spec s.data[i]! ∧ ¬ is_consonant_spec s.data[j]! ∧ is_consonant_spec s.data[k]!) ∧
    (result ≠ "" →
      result.length = 1 ∧
      result.data[0]! ∈ s.data ∧
      ¬ is_consonant_spec result.data[0]! ∧
      ∃ (i j k : Nat),
        i < j ∧ j < k ∧ k < s.length ∧
        is_consonant_spec s.data[i]! ∧ ¬ is_consonant_spec s.data[j]! ∧ is_consonant_spec s.data[k]! ∧
        result.data[0]! = s.data[j]! ∧
        (∀ (i' j' k' : Nat),
          i' < j' ∧ j' < k' ∧ k' < s.length ∧ is_consonant_spec s.data[i']! ∧ ¬ is_consonant_spec s.data[j']! ∧ is_consonant_spec s.data[k']! →
          j' ≤ j))
  
  by_cases h : s.data.all (fun c => c.isAlpha)
  · simp [h]
    by_cases h2 : find_first_cvc_pattern s = none
    · simp [h2]
      constructor
      · intro
        rfl
      · intro h3
        exfalso
        exact h3 rfl
    · simp [h2]
      obtain ⟨idx, hidx⟩ := Option.ne_none_iff_exists.mp h2
      simp [hidx]
      constructor
      · intro h3
        exfalso
        exact h3 rfl
      · intro
        constructor
        · simp [String.mk]
        constructor
        · simp [String.mk]
          sorry -- Need to prove element is in original string
        constructor
        · sorry -- Need to prove it's not a consonant
        · sorry -- Need to use find_first_cvc_pattern_correct
  · simp [h]
    constructor
    · intro
      rfl
    · intro h3
      exfalso
      exact h3 rfl
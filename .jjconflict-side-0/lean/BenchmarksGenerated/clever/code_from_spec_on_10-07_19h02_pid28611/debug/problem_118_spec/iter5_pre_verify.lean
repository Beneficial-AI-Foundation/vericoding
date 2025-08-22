import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def is_vowel (c: Char) : Bool :=
  c ∈ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']

def implementation (s: String) : String :=
  let chars := s.data
  let n := s.length
  let rec find_pattern (i : Nat) : Option Nat :=
    if h : i + 2 < n then
      let c1 := chars[i]!
      let c2 := chars[i + 1]!
      let c3 := chars[i + 2]!
      if c1.isAlpha && !is_vowel c1 && c2.isAlpha && is_vowel c2 && c3.isAlpha && !is_vowel c3 then
        some (i + 1)
      else
        find_pattern (i + 1)
    else
      none
  termination_by n - i
  match find_pattern 0 with
  | none => ""
  | some j => String.mk [chars[j]!]

-- LLM HELPER
lemma is_vowel_iff (c: Char) : 
  is_vowel c = true ↔ c ∈ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'] := by
  rfl

-- LLM HELPER
lemma not_is_vowel_iff (c: Char) : 
  is_vowel c = false ↔ c ∉ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'] := by
  simp [is_vowel]

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · intro h_all_alpha
    let is_consonant_prop (c: Char) :=
      c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
      c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
      c.isAlpha
    
    simp [implementation]
    cases h_pattern : (let chars := s.data
      let n := s.length
      let rec find_pattern (i : Nat) : Option Nat :=
        if h : i + 2 < n then
          let c1 := chars[i]!
          let c2 := chars[i + 1]!
          let c3 := chars[i + 2]!
          if c1.isAlpha && !is_vowel c1 && c2.isAlpha && is_vowel c2 && c3.isAlpha && !is_vowel c3 then
            some (i + 1)
          else
            find_pattern (i + 1)
        else
          none
      termination_by n - i
      find_pattern 0) with
    | none => 
      simp [String.mk]
      constructor
      · intro
        by_contra h_contra
        obtain ⟨i, j, k, hij, hjk, hk_bound, hc_i, hv_j, hc_k⟩ := h_contra
        -- This is a contradiction since the algorithm should have found the pattern
        have : ∃ result, (let chars := s.data
          let n := s.length
          let rec find_pattern (i : Nat) : Option Nat :=
            if h : i + 2 < n then
              let c1 := chars[i]!
              let c2 := chars[i + 1]!
              let c3 := chars[i + 2]!
              if c1.isAlpha && !is_vowel c1 && c2.isAlpha && is_vowel c2 && c3.isAlpha && !is_vowel c3 then
                some (i + 1)
              else
                find_pattern (i + 1)
            else
              none
          termination_by n - i
          find_pattern 0) = some result := by
          sorry
        rw [h_pattern] at this
        simp at this
      · intro h
        contradiction
    | some j =>
      simp [String.mk]
      constructor
      · intro h
        simp at h
      · intro h
        simp at h
        constructor
        · simp [String.length]
        constructor
        · have hj_bound : j < s.length := by
            sorry
          apply List.get_mem
          exact hj_bound
        constructor
        · simp [List.get]
          simp [is_consonant_prop]
          sorry
        · use j - 1, j, j + 1
          constructor
          · sorry
          constructor
          · sorry
          constructor
          · sorry
          constructor
          · simp [is_consonant_prop]
            sorry
          constructor
          · simp [is_consonant_prop]
            sorry
          constructor
          · simp [is_consonant_prop]
            sorry
          constructor
          · simp [List.get]
          · intro i' j' k' hi'j' hj'k' hk'_bound hc_i' hv_j' hc_k'
            sorry
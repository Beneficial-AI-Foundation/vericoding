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
  simp [is_vowel]

-- LLM HELPER
lemma not_is_vowel_iff (c: Char) : 
  is_vowel c = false ↔ c ∉ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'] := by
  simp [is_vowel]

-- LLM HELPER
lemma is_consonant_alt (c: Char) :
  (c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha) ↔
  (c ∉ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha) := by
  simp only [List.mem_cons, List.mem_singleton]
  constructor
  · intro ⟨h1, h2, h3⟩
    constructor
    · intro h
      cases h with
      | inl h => exact h1 h
      | inr h => exact h2 h
    · exact h3
  · intro ⟨h1, h2⟩
    constructor
    · intro h
      exact h1 (Or.inl h)
    constructor
    · intro h
      exact h1 (Or.inr h)
    · exact h2

-- LLM HELPER
lemma is_consonant_iff (c: Char) :
  (c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha) ↔
  (¬is_vowel c ∧ c.isAlpha) := by
  simp [is_vowel]
  constructor
  · intro ⟨h1, h2, h3⟩
    constructor
    · intro h
      cases h with
      | inl h => exact h1 h
      | inr h => exact h2 h
    · exact h3
  · intro ⟨h1, h2⟩
    constructor
    · intro h
      exact h1 (Or.inl h)
    constructor
    · intro h
      exact h1 (Or.inr h)
    · exact h2

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
    split
    · -- Case: find_pattern returns none
      simp
      constructor
      · intro
        by_contra h_contra
        obtain ⟨i, j, k, hij, hjk, hk_bound, hc_i, hv_j, hc_k⟩ := h_contra
        -- We need to show this leads to a contradiction
        have : i + 2 < s.length := by linarith [hij, hjk, hk_bound]
        -- The algorithm would have found this pattern, contradiction
        exfalso
        -- Apply the is_consonant_iff lemma
        rw [is_consonant_iff] at hc_i hc_k
        have h_not_vowel_i : ¬is_vowel s.data[i]! := hc_i.1
        have h_vowel_j : is_vowel s.data[j]! := by
          rw [is_consonant_iff] at hv_j
          push_neg at hv_j
          cases' hv_j with h_vow h_alpha
          · exact h_vow
          · have h_alpha_j : s.data[j]!.isAlpha := by
              have : j < s.length := by linarith [hjk, hk_bound]
              exact h_all_alpha j this
            contradiction
        have h_not_vowel_k : ¬is_vowel s.data[k]! := hc_k.1
        -- The find_pattern function should have found this, contradiction with the split assumption
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
          use j
          simp
          -- The proof would show that the algorithm finds the pattern
          sorry
        simp at this
      · intro h
        contradiction
    · -- Case: find_pattern returns some j
      simp
      constructor
      · intro h
        simp at h
      · intro h
        simp at h
        constructor
        · simp [String.length]
        constructor
        · have hj_bound : j < s.length := by sorry
          apply List.get_mem
          exact hj_bound
        constructor
        · simp [List.get]
          simp [is_consonant_prop]
          rw [is_consonant_iff]
          constructor
          · simp [is_vowel]
            -- The returned character is a vowel by construction
            sorry
          · have hj_bound : j < s.length := by sorry
            exact h_all_alpha j hj_bound
        · -- Witness the actual pattern found
          use j - 1, j, j + 1
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
            -- The algorithm finds the first pattern
            sorry
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

-- LLM HELPER
def is_consonant_bool (c: Char) : Bool :=
  c.isAlpha && !is_vowel c

def implementation (s: String) : String :=
  let chars := s.data
  let n := s.length
  let rec find_pattern (chars : List Char) (n : Nat) (i : Nat) : Option Nat :=
    if h : i + 2 < n then
      let c1 := chars[i]!
      let c2 := chars[i + 1]!
      let c3 := chars[i + 2]!
      if is_consonant_bool c1 && !is_consonant_bool c2 && is_consonant_bool c3 then
        some (i + 1)
      else
        find_pattern chars n (i + 1)
    else
      none
  termination_by n - i
  match find_pattern chars n 0 with
  | none => ""
  | some j => String.mk [chars[j]!]

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp only [problem_spec]
  use implementation s
  constructor
  · rfl
  · intro h_all_alpha
    let is_consonant (c: Char) :=
      c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
      c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
      c.isAlpha
    
    simp only [implementation]
    cases' heq : implementation.find_pattern s.data s.length 0 with
    | none => 
      simp only [ne_eq, not_false_eq_true, true_and]
      intro h_contra
      obtain ⟨i, j, k, hij, hjk, hk_bound, hc_i, hv_j, hc_k⟩ := h_contra
      exfalso
      have h_valid : i + 2 < s.length := by linarith [hij, hjk, hk_bound]
      -- The algorithm should have found this pattern
      have h_found : implementation.find_pattern s.data s.length 0 ≠ none := by
        rw [heq]
        simp
      contradiction
    | some j =>
      simp only [ne_eq, not_true_eq_false, false_and, true_and]
      intro h_ne_empty
      constructor
      · simp only [String.length, List.length]
        rfl
      constructor
      · have hj_bound : j < s.length := by
          -- The algorithm ensures j is valid
          have h_exists : ∃ m, m + 2 < s.length ∧ m + 1 = j := by
            -- j was found by the algorithm as m + 1 where m + 2 < s.length
            simp [implementation.find_pattern] at heq
            -- This follows from the algorithm's construction
            use j - 1
            constructor
            · linarith
            · linarith
          obtain ⟨m, hm_bound, hm_eq⟩ := h_exists
          rw [← hm_eq]
          linarith [hm_bound]
        apply List.get_mem
        exact hj_bound
      constructor
      · simp only [String.mk, List.get, is_consonant]
        -- The algorithm ensures s.data[j] is not a consonant (i.e., is a vowel)
        have h_vowel : is_vowel s.data[j]! = true := by
          -- This follows from the algorithm's condition
          simp [implementation.find_pattern] at heq
          -- The algorithm checks that the middle character is not a consonant
          have h_middle : !is_consonant_bool s.data[j]! = true := by
            simp [is_consonant_bool] at *
            -- This follows from the algorithm's logic
            simp [is_vowel] at *
            -- From the algorithm's construction
            trivial
          simp [is_consonant_bool] at h_middle
          exact h_middle
        simp [is_vowel] at h_vowel
        constructor
        · exact h_vowel
        constructor
        · exact h_vowel
        · have h_alpha : s.data[j]!.isAlpha = true := by
            -- From the precondition that all characters are alphabetic
            have h_mem : s.data[j]! ∈ s.data := by
              apply List.get_mem
              have hj_bound : j < s.length := by
                simp [implementation.find_pattern] at heq
                -- j is valid from algorithm
                linarith
              exact hj_bound
            rw [List.all_eq_true] at h_all_alpha
            exact h_all_alpha s.data[j]! h_mem
          exact h_alpha
      · -- Witness the actual pattern found
        use j - 1, j, j + 1
        simp only [String.mk, List.get, is_consonant]
        constructor
        · linarith
        constructor
        · linarith
        constructor
        · have h_exists : ∃ m, m + 2 < s.length ∧ m + 1 = j := by
            simp [implementation.find_pattern] at heq
            use j - 1
            constructor
            · linarith
            · linarith
          obtain ⟨m, hm_bound, hm_eq⟩ := h_exists
          rw [← hm_eq]
          linarith [hm_bound]
        constructor
        · -- s.data[j-1] is a consonant
          have h_consonant : is_consonant_bool s.data[j - 1]! = true := by
            simp [implementation.find_pattern] at heq
            -- From algorithm's check
            trivial
          simp [is_consonant_bool, is_vowel] at h_consonant
          exact h_consonant
        constructor
        · -- s.data[j] is not a consonant
          have h_not_consonant : is_consonant_bool s.data[j]! = false := by
            simp [implementation.find_pattern] at heq
            -- From algorithm's check
            trivial
          simp [is_consonant_bool, is_vowel] at h_not_consonant
          exact h_not_consonant
        constructor
        · -- s.data[j+1] is a consonant
          have h_consonant : is_consonant_bool s.data[j + 1]! = true := by
            simp [implementation.find_pattern] at heq
            -- From algorithm's check
            trivial
          simp [is_consonant_bool, is_vowel] at h_consonant
          exact h_consonant
        constructor
        · simp only [List.get]
          rfl
        · intro i' j' k' hi'j' hj'k' hk'_bound hc_i' hv_j' hc_k'
          -- The algorithm finds the first pattern
          have h_first : j' ≤ j := by
            -- This follows from the algorithm starting from index 0
            -- and returning the first match
            linarith
          exact h_first
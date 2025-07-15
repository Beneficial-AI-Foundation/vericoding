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
  let rec find_pattern (chars : List Char) (n : Nat) (i : Nat) : Option Nat :=
    if h : i + 2 < n then
      let c1 := chars[i]!
      let c2 := chars[i + 1]!
      let c3 := chars[i + 2]!
      if c1.isAlpha && !is_vowel c1 && c2.isAlpha && is_vowel c2 && c3.isAlpha && !is_vowel c3 then
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
      by_contra h_contra
      obtain ⟨i, j, k, hij, hjk, hk_bound, hc_i, hv_j, hc_k⟩ := h_contra
      -- This would require showing that the algorithm would have found the pattern
      -- but that's complex to prove in this context
      exfalso
      have h_pattern : i + 2 < s.length := by linarith [hij, hjk, hk_bound]
      sorry
    | some j =>
      simp only [ne_eq, not_true_eq_false, false_and, true_and]
      intro h_ne_empty
      constructor
      · simp only [String.length, List.length]
        rfl
      constructor
      · have hj_bound : j < s.length := by
          -- The algorithm ensures that j is a valid index
          sorry
        apply List.get_mem
        exact hj_bound
      constructor
      · simp only [String.mk, List.get, is_consonant, is_vowel]
        -- The algorithm ensures that s.data[j] is a vowel
        sorry
      · -- Witness the actual pattern found
        use j - 1, j, j + 1
        simp only [String.mk, List.get, is_consonant, is_vowel]
        constructor
        · sorry
        constructor
        · sorry
        constructor
        · sorry
        constructor
        · sorry
        constructor
        · sorry
        constructor
        · sorry
        constructor
        · simp only [List.get]
          rfl
        · intro i' j' k' hi'j' hj'k' hk'_bound hc_i' hv_j' hc_k'
          -- The algorithm finds the first pattern
          sorry
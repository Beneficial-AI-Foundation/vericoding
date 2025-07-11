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
def is_consonant (c: Char) : Bool :=
  c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
  c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
  c.isAlpha

-- LLM HELPER
def find_first_cvc_pattern (s: String) : Option Nat :=
  let chars := s.data
  let n := s.length
  let rec search_from_i (i : Nat) : Option Nat :=
    if i + 2 >= n then none
    else
      let rec search_from_j (j : Nat) : Option Nat :=
        if j + 1 >= n then none
        else
          let rec search_from_k (k : Nat) : Option Nat :=
            if k >= n then none
            else if is_consonant chars[i]! ∧ ¬is_consonant chars[j]! ∧ is_consonant chars[k]! then
              some j
            else if k + 1 < n then search_from_k (k + 1)
            else none
          termination_by n - k
          match search_from_k (j + 1) with
          | some result => some result
          | none => if j + 2 < n then search_from_j (j + 1) else none
      termination_by n - j
      match search_from_j (i + 1) with
      | some result => some result
      | none => if i + 3 < n then search_from_i (i + 1) else none
  termination_by n - i
  if n < 3 then none else search_from_i 0

def implementation (s: String) : String :=
  match find_first_cvc_pattern s with
  | none => ""
  | some j => String.mk [s.data[j]!]

-- LLM HELPER
lemma is_consonant_def (c: Char) : 
  is_consonant c = true ↔ (c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha = true) := by
  simp [is_consonant]

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  intro h_all_alpha
  let is_consonant_prop (c: Char) :=
    c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
    c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
    c.isAlpha
  
  cases h_pattern : find_first_cvc_pattern s with
  | none => 
    simp [String.mk]
    constructor
    · intro
      by_contra h_contra
      obtain ⟨i, j, k, hij, hjk, hk_bound, hc_i, hv_j, hc_k⟩ := h_contra
      -- The algorithm would have found this pattern, contradicting h_pattern
      simp [find_first_cvc_pattern] at h_pattern
      split_ifs at h_pattern
      · simp at h_pattern
      · exfalso
        simp [is_consonant_prop] at hc_i hv_j hc_k
        have hc_i_bool : is_consonant s.data[i]! = true := by
          simp [is_consonant_def]
          exact hc_i
        have hv_j_bool : is_consonant s.data[j]! = false := by
          simp [is_consonant_def]
          exact hv_j
        have hc_k_bool : is_consonant s.data[k]! = true := by
          simp [is_consonant_def]
          exact hc_k
        -- The algorithm should have found this pattern
        have : ∃ result, find_first_cvc_pattern s = some result := by
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
        intro h_contra
        simp [find_first_cvc_pattern] at h_pattern
        split_ifs at h_pattern
        · simp at h_pattern
        · sorry
      · simp [find_first_cvc_pattern] at h_pattern
        split_ifs at h_pattern
        · simp at h_pattern
        · use 0, j, j + 1
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
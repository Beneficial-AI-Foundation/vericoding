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
  let rec helper (i j k : Nat) : Option Nat :=
    if k >= n then none
    else if j >= k then helper i (j + 1) (j + 2)
    else if i >= j then helper (i + 1) i (i + 2)
    else if is_consonant chars[i]! ∧ ¬is_consonant chars[j]! ∧ is_consonant chars[k]! then
      some j
    else if k + 1 < n then helper i j (k + 1)
    else if j + 1 < k then helper i (j + 1) (j + 2)
    else helper (i + 1) i (i + 2)
  helper 0 1 2

def implementation (s: String) : String :=
  match find_first_cvc_pattern s with
  | none => ""
  | some j => String.mk [s.data[j]!]

-- LLM HELPER
lemma is_consonant_def (c: Char) : 
  is_consonant c = (c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha) := by
  rfl

-- LLM HELPER
lemma find_first_cvc_pattern_correct (s: String) :
  (find_first_cvc_pattern s = none → 
    ¬ ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ 
    is_consonant s.data[i]! ∧ ¬is_consonant s.data[j]! ∧ is_consonant s.data[k]!) ∧
  (∀ j, find_first_cvc_pattern s = some j →
    ∃ (i k : Nat), i < j ∧ j < k ∧ k < s.length ∧
    is_consonant s.data[i]! ∧ ¬is_consonant s.data[j]! ∧ is_consonant s.data[k]! ∧
    (∀ (i' j' k' : Nat),
      i' < j' ∧ j' < k' ∧ k' < s.length ∧ 
      is_consonant s.data[i']! ∧ ¬is_consonant s.data[j']! ∧ is_consonant s.data[k']! →
      j' ≤ j)) := by
  constructor
  · intro h
    sorry -- Complex proof about the algorithm correctness
  · intro j h
    sorry -- Complex proof about the algorithm correctness

-- LLM HELPER
lemma string_mk_singleton_props (c: Char) (s: String) (j: Nat) (hj: j < s.length) (hc: s.data[j]! = c) :
  let result := String.mk [c]
  result.length = 1 ∧ result.data[0]! = c ∧ result.data[0]! ∈ s.data := by
  constructor
  · simp [String.mk, String.length]
  constructor
  · simp [String.mk, List.get]
  · use j
    constructor
    · exact hj
    · rw [List.get_eq_getElem]
      exact hc.symm

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
    have h_no_pattern := (find_first_cvc_pattern_correct s).1 h_pattern
    constructor
    · intro
      convert h_no_pattern
      ext c
      simp [is_consonant_def, is_consonant_prop]
    · intro h
      contradiction
  | some j =>
    simp [String.mk]
    have h_pattern_exists := (find_first_cvc_pattern_correct s).2 j h_pattern
    obtain ⟨i, k, hi, hj, hk, hc_i, hv_j, hc_k, h_minimal⟩ := h_pattern_exists
    constructor
    · intro h
      simp at h
    · intro h
      simp at h
      constructor
      · simp [String.length]
      constructor
      · have hj_bound : j < s.length := by
          linarith [hj, hk]
        have h_in_data : s.data[j]! ∈ s.data := by
          use j
          exact ⟨hj_bound, rfl⟩
        exact h_in_data
      constructor
      · simp [List.get]
        convert hv_j
        simp [is_consonant_def, is_consonant_prop]
      · use i, j, k
        constructor
        · exact hi
        constructor
        · exact hj
        constructor
        · exact hk
        constructor
        · convert hc_i
          simp [is_consonant_def, is_consonant_prop]
        constructor
        · convert hv_j
          simp [is_consonant_def, is_consonant_prop]
        constructor
        · convert hc_k
          simp [is_consonant_def, is_consonant_prop]
        constructor
        · simp [List.get]
        · intro i' j' k' hi'j' hj'k' hk'_bound hc_i' hv_j' hc_k'
          have h_convert : is_consonant s.data[i']! ∧ ¬is_consonant s.data[j']! ∧ is_consonant s.data[k']! := by
            constructor
            · convert hc_i'
              simp [is_consonant_def, is_consonant_prop]
            constructor
            · convert hv_j'
              simp [is_consonant_def, is_consonant_prop]
            · convert hc_k'
              simp [is_consonant_def, is_consonant_prop]
          exact h_minimal i' j' k' hi'j' hj'k' hk'_bound h_convert.1 h_convert.2.1 h_convert.2.2
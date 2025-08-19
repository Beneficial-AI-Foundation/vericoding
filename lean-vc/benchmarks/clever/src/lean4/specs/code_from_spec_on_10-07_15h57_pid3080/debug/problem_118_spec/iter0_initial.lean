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
def find_first_cvc_vowel (s: String) : Option Char :=
  let chars := s.data
  let n := chars.length
  let rec aux (i : Nat) : Option Char :=
    if i + 2 < n then
      if is_consonant chars[i]! ∧ ¬is_consonant chars[i+1]! ∧ is_consonant chars[i+2]! then
        some chars[i+1]!
      else
        aux (i + 1)
    else
      none
  aux 0

def implementation (s: String) : String := 
  match find_first_cvc_vowel s with
  | some c => String.mk [c]
  | none => ""

-- LLM HELPER
lemma is_consonant_prop (c: Char) : is_consonant c = true ↔ 
  (c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha) := by
  simp [is_consonant]

-- LLM HELPER
lemma find_first_cvc_vowel_none_iff (s: String) : 
  find_first_cvc_vowel s = none ↔ 
  ¬∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ 
    is_consonant s.data[i]! ∧ ¬is_consonant s.data[j]! ∧ is_consonant s.data[k]! := by
  simp [find_first_cvc_vowel]
  constructor
  · intro h
    by_contra h_contra
    obtain ⟨i, j, k, hij, hjk, hk_lt, hi_cons, hj_not_cons, hk_cons⟩ := h_contra
    have : j = i + 1 ∧ k = i + 2 := by
      cases' hij with
      | refl => cases' hjk
      | step hij' => 
        cases' hjk with
        | refl => omega
        | step hjk' => 
          have : i + 2 < s.length := by omega
          rw [find_first_cvc_vowel] at h
          simp at h
          sorry
    sorry
  · intro h
    simp [find_first_cvc_vowel]
    sorry

-- LLM HELPER
lemma find_first_cvc_vowel_some_iff (s: String) (c: Char) : 
  find_first_cvc_vowel s = some c ↔ 
  (∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ 
    is_consonant s.data[i]! ∧ ¬is_consonant s.data[j]! ∧ is_consonant s.data[k]! ∧
    c = s.data[j]! ∧
    (∀ (i' j' k' : Nat), i' < j' ∧ j' < k' ∧ k' < s.length ∧ 
      is_consonant s.data[i']! ∧ ¬is_consonant s.data[j']! ∧ is_consonant s.data[k']! → j' ≤ j)) := by
  sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · intro h_all_alpha
    simp [implementation]
    cases h_find : find_first_cvc_vowel s with
    | none => 
      simp
      rw [find_first_cvc_vowel_none_iff] at h_find
      exact h_find
    | some c =>
      simp
      rw [find_first_cvc_vowel_some_iff] at h_find
      obtain ⟨i, j, k, hij, hjk, hk_lt, hi_cons, hj_not_cons, hk_cons, hc_eq, h_minimal⟩ := h_find
      constructor
      · simp [String.mk]
      constructor
      · simp [String.mk]
        rw [← hc_eq]
        exact List.mem_of_mem_nth_le s.data j (by omega)
      constructor
      · simp [String.mk]
        rw [← hc_eq]
        rw [← is_consonant_prop]
        exact hj_not_cons
      · use i, j, k
        constructor
        · exact hij
        constructor
        · exact hjk
        constructor
        · exact hk_lt
        constructor
        · rw [is_consonant_prop]
          exact hi_cons
        constructor
        · rw [is_consonant_prop]
          exact hj_not_cons
        constructor
        · rw [is_consonant_prop]
          exact hk_cons
        constructor
        · simp [String.mk]
          exact hc_eq
        · intro i' j' k' hij' hjk' hk'_lt hi'_cons hj'_not_cons hk'_cons
          apply h_minimal
          · exact hij'
          · exact hjk'
          · exact hk'_lt
          · rw [← is_consonant_prop]
            exact hi'_cons
          · rw [← is_consonant_prop]
            exact hj'_not_cons
          · rw [← is_consonant_prop]
            exact hk'_cons
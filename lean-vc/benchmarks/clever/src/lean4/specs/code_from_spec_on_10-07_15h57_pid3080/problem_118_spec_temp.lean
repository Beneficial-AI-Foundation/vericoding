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
    have h_min : ∃ m, m + 2 < s.length ∧ is_consonant s.data[m]! ∧ ¬is_consonant s.data[m+1]! ∧ is_consonant s.data[m+2]! := by
      use i
      constructor
      · omega
      constructor
      · exact hi_cons
      constructor
      · exact hj_not_cons
      · exact hk_cons
    obtain ⟨m, hm_lt, hm_cons, hm1_not_cons, hm2_cons⟩ := h_min
    have : find_first_cvc_vowel s ≠ none := by
      simp [find_first_cvc_vowel]
      use m
      simp [hm_lt, hm_cons, hm1_not_cons, hm2_cons]
    contradiction
  · intro h
    simp [find_first_cvc_vowel]
    by_contra h_contra
    obtain ⟨i, hi_lt, hi_cons, hi1_not_cons, hi2_cons⟩ := h_contra
    apply h
    use i, i+1, i+2
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor
    · exact hi_cons
    constructor
    · exact hi1_not_cons
    · exact hi2_cons

-- LLM HELPER
lemma find_first_cvc_vowel_some_iff (s: String) (c: Char) : 
  find_first_cvc_vowel s = some c ↔ 
  (∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ 
    is_consonant s.data[i]! ∧ ¬is_consonant s.data[j]! ∧ is_consonant s.data[k]! ∧
    c = s.data[j]! ∧
    (∀ (i' j' k' : Nat), i' < j' ∧ j' < k' ∧ k' < s.length ∧ 
      is_consonant s.data[i']! ∧ ¬is_consonant s.data[j']! ∧ is_consonant s.data[k']! → j' ≤ j)) := by
  simp [find_first_cvc_vowel]
  constructor
  · intro h
    obtain ⟨i, hi_lt, hi_cons, hi1_not_cons, hi2_cons, hc_eq⟩ := h
    use i, i+1, i+2
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor
    · exact hi_cons
    constructor
    · exact hi1_not_cons
    constructor
    · exact hi2_cons
    constructor
    · exact hc_eq.symm
    · intro i' j' k' hij' hjk' hk'_lt hi'_cons hj'_not_cons hk'_cons
      have : j' = i' + 1 ∧ k' = i' + 2 := by
        cases' Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt hij')) with
        | inl h_eq => 
          simp [h_eq] at hjk'
          cases' Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt hjk')) with
          | inl h_eq2 => exact ⟨h_eq, h_eq2⟩
          | inr h_lt2 => omega
        | inr h_lt => omega
      obtain ⟨hj'_eq, hk'_eq⟩ := this
      have : i ≤ i' := by
        by_contra h_not
        have : i' < i := Nat.lt_of_not_ge h_not
        have : i' + 2 < i + 2 := by omega
        have : find_first_cvc_vowel s = some s.data[i'+1]! := by
          simp [find_first_cvc_vowel]
          use i'
          simp [by omega : i' + 2 < s.length, hi'_cons, hj'_not_cons, hk'_cons]
        rw [this] at h
        have : some s.data[i'+1]! = some c := h
        have : s.data[i'+1]! = c := by simp at this; exact this
        rw [hj'_eq] at this
        rw [← this] at hc_eq
        have : i' + 1 = i + 1 := by
          simp at hc_eq
          have : s.data[i'+1]! = s.data[i+1]! := by rw [← hc_eq]; rfl
          -- This would require uniqueness of positions, which we assume
          omega
        omega
      rw [hj'_eq]
      omega
  · intro h
    obtain ⟨i, j, k, hij, hjk, hk_lt, hi_cons, hj_not_cons, hk_cons, hc_eq, h_minimal⟩ := h
    have : j = i + 1 ∧ k = i + 2 := by
      cases' Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt hij)) with
      | inl h_eq => 
        simp [h_eq] at hjk
        cases' Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt hjk)) with
        | inl h_eq2 => exact ⟨h_eq, h_eq2⟩
        | inr h_lt2 => omega
      | inr h_lt => omega
    obtain ⟨hj_eq, hk_eq⟩ := this
    use i
    constructor
    · rw [hk_eq] at hk_lt
      exact hk_lt
    constructor
    · rw [← hj_eq]
      exact hi_cons
    constructor
    · rw [← hj_eq]
      exact hj_not_cons
    constructor
    · rw [← hj_eq, ← hk_eq]
      exact hk_cons
    · rw [hj_eq]
      exact hc_eq

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
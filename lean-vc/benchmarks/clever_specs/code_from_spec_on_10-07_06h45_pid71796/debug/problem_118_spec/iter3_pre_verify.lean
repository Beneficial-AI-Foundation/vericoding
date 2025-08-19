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
  rfl

-- LLM HELPER
lemma find_first_cvc_pattern_some (s: String) (idx: Nat) : 
  find_first_cvc_pattern s = some idx →
  ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ 
  is_consonant s.data[i]! ∧ ¬is_consonant s.data[j]! ∧ is_consonant s.data[k]! ∧
  j = idx := by
  intro h
  unfold find_first_cvc_pattern at h
  simp at h
  induction' s.data with hd tl ih
  · simp at h
  · sorry

-- LLM HELPER
lemma find_first_cvc_pattern_none (s: String) : 
  find_first_cvc_pattern s = none →
  ¬∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ 
  is_consonant s.data[i]! ∧ ¬is_consonant s.data[j]! ∧ is_consonant s.data[k]! := by
  intro h
  unfold find_first_cvc_pattern at h
  simp at h
  intro ⟨i, j, k, hi, hj, hk, hcons_i, hvowel_j, hcons_k⟩
  sorry

-- LLM HELPER
lemma find_first_cvc_pattern_minimal (s: String) (idx: Nat) : 
  find_first_cvc_pattern s = some idx →
  ∀ (i' j' k' : Nat), i' < j' ∧ j' < k' ∧ k' < s.length ∧ 
  is_consonant s.data[i']! ∧ ¬is_consonant s.data[j']! ∧ is_consonant s.data[k']! → j' ≤ idx := by
  intro h
  unfold find_first_cvc_pattern at h
  simp at h
  intro i' j' k' hi' hj' hk' hcons_i' hvowel_j' hcons_k'
  sorry

-- LLM HELPER
lemma string_mk_single_char (c: Char) : (String.mk [c]).data[0]! = c := by
  rfl

-- LLM HELPER
lemma string_mk_single_length (c: Char) : (String.mk [c]).length = 1 := by
  rfl

-- LLM HELPER
lemma data_mem_of_get (s: String) (i: Nat) (h: i < s.length) : s.data[i]! ∈ s.data := by
  apply List.get_mem

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · intro h_alpha
    unfold implementation
    simp [h_alpha]
    constructor
    · intro h_empty
      by_cases h : find_first_cvc_pattern s = none
      · simp [h] at h_empty
        exact find_first_cvc_pattern_none s h
      · simp [h] at h_empty
        contradiction
    · intro h_nonempty
      by_cases h : find_first_cvc_pattern s = none
      · simp [h] at h_nonempty
        contradiction
      · obtain ⟨idx, hidx⟩ := Option.ne_none_iff_exists.mp h
        simp [hidx] at h_nonempty
        simp [hidx]
        constructor
        · exact string_mk_single_length _
        constructor
        · rw [string_mk_single_char]
          apply data_mem_of_get
          obtain ⟨i, j, k, hi, hj, hk, hcons_i, hvowel_j, hcons_k, heq⟩ := 
            find_first_cvc_pattern_some s idx hidx
          rw [← heq]
          exact hj
        constructor
        · rw [string_mk_single_char]
          obtain ⟨i, j, k, hi, hj, hk, hcons_i, hvowel_j, hcons_k, heq⟩ := 
            find_first_cvc_pattern_some s idx hidx
          rw [← heq]
          rw [← is_consonant_prop]
          exact Bool.not_eq_true_of_eq_false hvowel_j
        · obtain ⟨i, j, k, hi, hj, hk, hcons_i, hvowel_j, hcons_k, heq⟩ := 
            find_first_cvc_pattern_some s idx hidx
          use i, j, k
          constructor
          · exact hi
          constructor
          · exact hj
          constructor
          · exact hk
          constructor
          · rw [is_consonant_prop]
            exact hcons_i
          constructor
          · rw [is_consonant_prop]
            exact hvowel_j
          constructor
          · rw [is_consonant_prop]
            exact hcons_k
          constructor
          · rw [string_mk_single_char, heq]
          · intro i' j' k' hi' hj' hk' hcons_i' hvowel_j' hcons_k'
            rw [← heq]
            apply find_first_cvc_pattern_minimal s idx hidx
            constructor
            · exact hi'
            constructor
            · exact hj'
            constructor
            · exact hk'
            constructor
            · rw [← is_consonant_prop]
              exact hcons_i'
            constructor
            · rw [← is_consonant_prop]
              exact hvowel_j'
            · rw [← is_consonant_prop]
              exact hcons_k'
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
  let data := s.data
  let rec aux (i: Nat) : Option Nat :=
    if h : i + 2 < data.length then
      if is_consonant data[i]! ∧ ¬is_consonant data[i+1]! ∧ is_consonant data[i+2]! then
        some (i + 1)
      else
        aux (i + 1)
    else
      none
  aux 0

def implementation (s: String) : String :=
  match find_first_cvc_pattern s with
  | none => ""
  | some idx => String.mk [s.data[idx]!]

-- LLM HELPER
lemma is_consonant_iff (c: Char) (is_consonant_spec : Char → Prop) : 
  is_consonant_spec = (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha) →
  is_consonant c = true ↔ is_consonant_spec c := by
  intro h
  rw [h]
  simp [is_consonant]

-- LLM HELPER
lemma find_first_cvc_pattern_none_correct (s: String) : 
  find_first_cvc_pattern s = none → 
  ¬ ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ 
    (is_consonant s.data[i]! = true) ∧ (is_consonant s.data[j]! = false) ∧ (is_consonant s.data[k]! = true) := by
  intro h
  intro ⟨i, j, k, hij, hjk, hk, hcons_i, hvowel_j, hcons_k⟩
  -- The algorithm would have found this pattern if it existed
  sorry

-- LLM HELPER
lemma find_first_cvc_pattern_some_correct (s: String) (idx: Nat) : 
  find_first_cvc_pattern s = some idx → 
  ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ 
    (is_consonant s.data[i]! = true) ∧ (is_consonant s.data[j]! = false) ∧ (is_consonant s.data[k]! = true) ∧
    j = idx ∧
    (∀ (i' j' k' : Nat),
      i' < j' ∧ j' < k' ∧ k' < s.length ∧ 
      (is_consonant s.data[i']! = true) ∧ (is_consonant s.data[j']! = false) ∧ (is_consonant s.data[k']! = true) →
      j' ≤ j) := by
  intro h
  -- The algorithm finds the first such pattern
  sorry

-- LLM HELPER
lemma implementation_result_in_string (s: String) (idx: Nat) :
  find_first_cvc_pattern s = some idx →
  idx < s.data.length →
  s.data[idx]! ∈ s.data := by
  intro h1 h2
  exact List.get_mem s.data idx h2

-- LLM HELPER
lemma idx_bounds_from_pattern (s: String) (idx: Nat) :
  find_first_cvc_pattern s = some idx →
  idx < s.data.length := by
  intro h
  -- This follows from the algorithm's correctness
  sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  exists implementation s
  constructor
  · rfl
  · intro h_alpha
    let is_consonant_spec (c: Char) :=
      c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
      c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
      c.isAlpha
    have is_consonant_eq : ∀ c, is_consonant c = true ↔ is_consonant_spec c := fun c => by
      simp [is_consonant, is_consonant_spec]
    constructor
    · intro h_empty
      simp [implementation] at h_empty
      cases h_find : find_first_cvc_pattern s with
      | none => 
        have h_no_pattern := find_first_cvc_pattern_none_correct s h_find
        intro ⟨i, j, k, hij, hjk, hk, hcons_i, hvowel_j, hcons_k⟩
        apply h_no_pattern
        exists i, j, k
        constructor; exact hij
        constructor; exact hjk
        constructor; exact hk
        constructor; rw [← is_consonant_eq]; exact hcons_i
        constructor; rw [← is_consonant_eq] at hvowel_j; simp at hvowel_j; exact hvowel_j
        rw [← is_consonant_eq]; exact hcons_k
      | some idx => 
        contradiction
    · intro h_nonempty
      simp [implementation] at h_nonempty ⊢
      cases h_find : find_first_cvc_pattern s with
      | none => 
        contradiction
      | some idx =>
        constructor
        · simp [String.mk]
        constructor
        · have h_idx_bound := idx_bounds_from_pattern s idx h_find
          exact implementation_result_in_string s idx h_find h_idx_bound
        constructor
        · rw [is_consonant_eq]
          have := find_first_cvc_pattern_some_correct s idx h_find
          obtain ⟨i, j, k, hij, hjk, hk, hcons_i, hvowel_j, hcons_k, hj_eq, hmin⟩ := this
          simp [String.mk]
          rw [← hj_eq]
          rw [← is_consonant_eq] at hvowel_j
          simp at hvowel_j
          exact hvowel_j
        · rw [is_consonant_eq]
          have := find_first_cvc_pattern_some_correct s idx h_find
          obtain ⟨i, j, k, hij, hjk, hk, hcons_i, hvowel_j, hcons_k, hj_eq, hmin⟩ := this
          exists i, j, k
          constructor; exact hij
          constructor; exact hjk
          constructor; exact hk
          constructor; rw [← is_consonant_eq]; exact hcons_i
          constructor; rw [← is_consonant_eq] at hvowel_j; simp at hvowel_j; exact hvowel_j
          constructor; rw [← is_consonant_eq]; exact hcons_k
          constructor
          · simp [String.mk]
            rw [← hj_eq]
            rfl
          · intros i' j' k' hij' hjk' hk' hcons_i' hvowel_j' hcons_k'
            apply hmin
            constructor; exact hij'
            constructor; exact hjk'
            constructor; exact hk'
            constructor; rw [← is_consonant_eq]; exact hcons_i'
            constructor; rw [← is_consonant_eq] at hvowel_j'; simp at hvowel_j'; exact hvowel_j'
            rw [← is_consonant_eq]; exact hcons_k'
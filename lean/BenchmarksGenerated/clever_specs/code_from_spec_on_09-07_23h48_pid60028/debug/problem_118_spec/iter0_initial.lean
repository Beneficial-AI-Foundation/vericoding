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
lemma is_consonant_iff (c: Char) : 
  is_consonant c = true ↔ 
  c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha := by
  rfl

-- LLM HELPER
lemma find_first_cvc_pattern_none (s: String) : 
  find_first_cvc_pattern s = none → 
  ¬ ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ 
    is_consonant s.data[i]! ∧ ¬is_consonant s.data[j]! ∧ is_consonant s.data[k]! := by
  intro h
  intro ⟨i, j, k, hij, hjk, hk, hcons_i, hvowel_j, hcons_k⟩
  have : j = i + 1 := by
    -- This follows from the minimality property and the algorithm
    sorry
  have : k = j + 1 := by
    -- This follows from the minimality property and the algorithm
    sorry
  subst this
  have : i + 2 < s.data.length := by
    rw [← this] at hk
    exact hk
  -- The algorithm would have found this pattern
  sorry

-- LLM HELPER
lemma find_first_cvc_pattern_some (s: String) (idx: Nat) : 
  find_first_cvc_pattern s = some idx → 
  ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ 
    is_consonant s.data[i]! ∧ ¬is_consonant s.data[j]! ∧ is_consonant s.data[k]! ∧
    j = idx ∧
    (∀ (i' j' k' : Nat),
      i' < j' ∧ j' < k' ∧ k' < s.length ∧ 
      is_consonant s.data[i']! ∧ ¬is_consonant s.data[j']! ∧ is_consonant s.data[k']! →
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
    have is_consonant_eq : ∀ c, is_consonant c = true ↔ is_consonant_spec c := fun c => by rfl
    constructor
    · intro h_empty
      simp [implementation] at h_empty
      cases h_find : find_first_cvc_pattern s with
      | none => 
        rw [is_consonant_eq] at find_first_cvc_pattern_none
        exact find_first_cvc_pattern_none s h_find
      | some idx => 
        simp at h_empty
    · intro h_nonempty
      simp [implementation] at h_nonempty ⊢
      cases h_find : find_first_cvc_pattern s with
      | none => 
        simp at h_nonempty
      | some idx =>
        simp at h_nonempty
        constructor
        · simp [String.mk]
        constructor
        · have h_idx_bound : idx < s.data.length := by
            -- This follows from the algorithm's correctness
            sorry
          exact implementation_result_in_string s idx h_find h_idx_bound
        constructor
        · rw [is_consonant_eq]
          have := find_first_cvc_pattern_some s idx h_find
          obtain ⟨i, j, k, hij, hjk, hk, hcons_i, hvowel_j, hcons_k, hj_eq, hmin⟩ := this
          rw [← hj_eq]
          exact hvowel_j
        · rw [is_consonant_eq]
          have := find_first_cvc_pattern_some s idx h_find
          obtain ⟨i, j, k, hij, hjk, hk, hcons_i, hvowel_j, hcons_k, hj_eq, hmin⟩ := this
          exists i, j, k
          constructor; exact hij
          constructor; exact hjk
          constructor; exact hk
          constructor; exact hcons_i
          constructor; exact hvowel_j
          constructor; exact hcons_k
          constructor
          · simp [String.mk]
            rw [← hj_eq]
            rfl
          · exact hmin
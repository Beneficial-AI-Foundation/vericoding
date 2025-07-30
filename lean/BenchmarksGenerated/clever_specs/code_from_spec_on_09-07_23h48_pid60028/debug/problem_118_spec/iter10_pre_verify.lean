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
lemma find_first_cvc_pattern_none_correct (s: String) : 
  find_first_cvc_pattern s = none → 
  ¬ ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ 
    (is_consonant s.data[i]! = true) ∧ (is_consonant s.data[j]! = false) ∧ (is_consonant s.data[k]! = true) := by
  intro h
  by_contra h_exists
  obtain ⟨i, j, k, hij, hjk, hk, hcons_i, hvowel_j, hcons_k⟩ := h_exists
  have hj_bound : j < s.data.length := by
    exact Nat.lt_trans hjk hk
  have hi_bound : i < s.data.length := by
    exact Nat.lt_trans hij hj_bound
  have hik : i + 2 ≤ k := by
    have : i + 1 ≤ j := Nat.succ_le_of_lt hij
    have : j + 1 ≤ k := Nat.succ_le_of_lt hjk
    linarith
  have h_pattern : i + 2 < s.data.length := by
    exact Nat.lt_of_le_of_lt hik hk
  -- This would contradict the algorithm returning none
  have h_cons_seq : i < j ∧ j = i + 1 ∧ k = i + 2 := by
    cases' Nat.lt_iff_le_and_ne.mp hij with h_le h_ne
    cases' Nat.lt_iff_le_and_ne.mp hjk with h_le2 h_ne2
    have : i + 1 ≤ j := Nat.succ_le_of_lt hij
    have : j + 1 ≤ k := Nat.succ_le_of_lt hjk
    have : i + 2 ≤ k := by linarith
    have : k ≤ i + 2 := by linarith [hik]
    have : k = i + 2 := Nat.eq_of_le_of_lt_succ ⟨this, Nat.lt_succ_of_le this⟩
    have : j = i + 1 := by
      cases' Nat.eq_or_lt_of_le this with h_eq h_lt
      · rw [← h_eq] at hjk
        simp at hjk
      · linarith
    exact ⟨hij, this, ‹k = i + 2›⟩
  -- The algorithm would have found this pattern
  rw [find_first_cvc_pattern] at h
  simp at h

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
  rw [find_first_cvc_pattern] at h
  simp at h
  use (idx - 1), idx, (idx + 1)
  constructor
  · exact Nat.sub_lt (Nat.pos_of_ne_zero (by simp)) (by simp)
  constructor
  · exact Nat.lt_succ_self idx
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp
  constructor
  · rfl
  · intro i' j' k' h_pattern
    simp

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
  rw [find_first_cvc_pattern] at h
  simp at h
  exact Nat.zero_lt_succ idx

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
      constructor
      · intro h
        rw [is_consonant] at h
        exact h
      · intro h
        rw [is_consonant]
        exact h
    constructor
    · intro h_empty
      rw [implementation] at h_empty
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
        constructor; rw [← is_consonant_eq] at hvowel_j; rw [Bool.not_eq_true] at hvowel_j; exact hvowel_j
        rw [← is_consonant_eq]; exact hcons_k
      | some idx => 
        rw [String.mk] at h_empty
        simp at h_empty
    · intro h_nonempty
      rw [implementation] at h_nonempty ⊢
      cases h_find : find_first_cvc_pattern s with
      | none => 
        rw [String.mk] at h_nonempty
        simp at h_nonempty
      | some idx =>
        constructor
        · rw [String.mk]
          simp
        constructor
        · have h_idx_bound := idx_bounds_from_pattern s idx h_find
          exact implementation_result_in_string s idx h_find h_idx_bound
        constructor
        · rw [String.mk]
          simp
          rw [is_consonant_eq]
          have := find_first_cvc_pattern_some_correct s idx h_find
          obtain ⟨i, j, k, hij, hjk, hk, hcons_i, hvowel_j, hcons_k, hj_eq, hmin⟩ := this
          rw [← hj_eq]
          rw [← is_consonant_eq] at hvowel_j
          rw [Bool.not_eq_true] at hvowel_j
          exact hvowel_j
        · rw [is_consonant_eq]
          have := find_first_cvc_pattern_some_correct s idx h_find
          obtain ⟨i, j, k, hij, hjk, hk, hcons_i, hvowel_j, hcons_k, hj_eq, hmin⟩ := this
          exists i, j, k
          constructor; exact hij
          constructor; exact hjk
          constructor; exact hk
          constructor; rw [← is_consonant_eq]; exact hcons_i
          constructor; rw [← is_consonant_eq] at hvowel_j; rw [Bool.not_eq_true] at hvowel_j; exact hvowel_j
          constructor; rw [← is_consonant_eq]; exact hcons_k
          constructor
          · rw [String.mk]
            simp
            rw [← hj_eq]
            rfl
          · intros i' j' k' hij' hjk' hk' hcons_i' hvowel_j' hcons_k'
            apply hmin
            constructor; exact hij'
            constructor; exact hjk'
            constructor; exact hk'
            constructor; rw [← is_consonant_eq]; exact hcons_i'
            constructor; rw [← is_consonant_eq] at hvowel_j'; rw [Bool.not_eq_true] at hvowel_j'; exact hvowel_j'
            rw [← is_consonant_eq]; exact hcons_k'
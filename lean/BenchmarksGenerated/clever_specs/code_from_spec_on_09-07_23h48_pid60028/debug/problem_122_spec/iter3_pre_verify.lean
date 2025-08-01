def problem_spec
(implementation: List Int → Nat → Int)
(arr: List Int)
(k: Nat) :=
let spec (result: Int) :=
  1 ≤ arr.length → arr.length ≤ 100 → 1 ≤ k → k ≤ arr.length →
  ((∀ i, 0 ≤ i ∧ i < k → ¬(arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!)) → result = 0) ∧
  ∃ i, i < k
    ∧ arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!
    ∧ result = arr[i]! + (if i = 0 then 0 else implementation arr i)
    ∧ ∀ i', i < i' ∧ i' < k → ¬(arr[i']! ≤ 99 ∧ -99 ≤ arr[i']!)
∃ result, implementation arr k = result ∧
spec result

-- LLM HELPER
def is_valid_element (x: Int) : Bool :=
  x ≤ 99 ∧ -99 ≤ x

-- LLM HELPER
def find_last_valid_index (arr: List Int) (k: Nat) : Option Nat :=
  let rec helper (i: Nat) : Option Nat :=
    if i = 0 then
      none
    else
      let idx := i - 1
      if idx < k ∧ idx < arr.length ∧ is_valid_element arr[idx]! then
        some idx
      else
        helper idx
  helper k

-- LLM HELPER
lemma find_last_valid_index_decreasing (arr: List Int) (k: Nat) :
  ∀ i, match find_last_valid_index arr k with
  | none => True
  | some j => j < k := by
  intro i
  induction' k with k ih
  · simp [find_last_valid_index]
  · simp [find_last_valid_index]
    cases h : find_last_valid_index arr (k + 1) with
    | none => trivial
    | some j =>
      simp [find_last_valid_index] at h
      split at h
      · simp at h
      · split at h
        · simp at h
          injection h with h_eq
          rw [← h_eq]
          omega
        · have ih_k := ih
          rw [h] at ih_k
          exact ih_k

def implementation (arr: List Int) (k: Nat) : Int :=
  match find_last_valid_index arr k with
  | none => 0
  | some i => arr[i]! + (if i = 0 then 0 else implementation arr i)
termination_by k
decreasing_by
  simp_wf
  have h_find := find_last_valid_index arr k
  cases h_find with
  | none => simp
  | some i =>
    have h_correct := find_last_valid_index_decreasing arr k
    rw [← h_find] at h_correct
    simp at h_correct
    exact h_correct

-- LLM HELPER
lemma find_last_valid_index_correct (arr: List Int) (k: Nat) :
  match find_last_valid_index arr k with
  | none => ∀ i, i < k → i < arr.length → ¬is_valid_element arr[i]!
  | some j => j < k ∧ j < arr.length ∧ is_valid_element arr[j]! ∧ 
              ∀ i, j < i → i < k → i < arr.length → ¬is_valid_element arr[i]! := by
  induction' k with k ih
  · simp [find_last_valid_index]
  · simp [find_last_valid_index]
    cases h : find_last_valid_index arr (k + 1) with
    | none => 
      intros i hi hlen
      have : i ≤ k := Nat.le_of_lt_succ hi
      cases' Nat.lt_or_eq_of_le this with h_lt h_eq
      · have ih_k := ih
        rw [h] at ih_k
        exact ih_k i h_lt hlen
      · rw [← h_eq]
        simp [find_last_valid_index] at h
        split at h
        · simp at h
        · split at h
          · simp at h
          · assumption
    | some j =>
      simp [find_last_valid_index] at h
      split at h
      · simp at h
      · split at h
        · simp at h
          injection h with h_eq
          rw [← h_eq]
          constructor
          · omega
          constructor
          · assumption
          constructor
          · assumption
          · intros i hi hik hlen
            have : i ≤ k := Nat.le_of_lt_succ hik
            cases' Nat.lt_or_eq_of_le this with h_lt h_eq
            · have ih_k := ih
              rw [h] at ih_k
              exact ih_k.2.2.2 i hi h_lt hlen
            · rw [← h_eq]
              have : k < j := hi
              have : j = k := by omega
              rw [this] at hi
              have : k < k := hi
              omega
        · have ih_k := ih
          rw [h] at ih_k
          exact ih_k

theorem correctness
(arr: List Int)
(k: Nat)
: problem_spec implementation arr k := by
  use implementation arr k
  constructor
  · rfl
  · intro h1 h2 h3 h4
    constructor
    · intro h_no_valid
      simp [implementation]
      have h_none : find_last_valid_index arr k = none := by
        cases h_find : find_last_valid_index arr k with
        | none => rfl
        | some j =>
          have h_correct := find_last_valid_index_correct arr k
          rw [h_find] at h_correct
          have ⟨hj1, hj2, hj3, _⟩ := h_correct
          have hj_bound : j < k := hj1
          have hj_valid : is_valid_element arr[j]! := hj3
          have hj_not_valid : ¬is_valid_element arr[j]! := by
            apply h_no_valid
            constructor
            · exact Nat.zero_le j
            · exact hj_bound
          contradiction
      rw [h_none]
      simp
    · by_cases h_exists : ∃ i, i < k ∧ arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!
      · cases h_find : find_last_valid_index arr k with
        | none =>
          have h_correct := find_last_valid_index_correct arr k
          rw [h_find] at h_correct
          exfalso
          obtain ⟨i, hi1, hi2⟩ := h_exists
          have hi_len : i < arr.length := by
            have : k ≤ arr.length := h4
            omega
          have : is_valid_element arr[i]! := hi2
          have : ¬is_valid_element arr[i]! := h_correct i hi1 hi_len
          contradiction
        | some i =>
          use i
          have h_correct := find_last_valid_index_correct arr k
          rw [h_find] at h_correct
          have ⟨hi1, hi2, hi3, hi4⟩ := h_correct
          constructor
          · exact hi1
          constructor
          · exact hi3
          constructor
          · simp [implementation]
            rw [h_find]
            simp
          · intro i' hi'1 hi'2
            apply hi4
            · exact hi'1
            · exact hi'2
            · have : k ≤ arr.length := h4
              omega
      · exfalso
        push_neg at h_exists
        have h_no_valid : ∀ i, 0 ≤ i ∧ i < k → ¬(arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!) := by
          intros i hi
          exact h_exists i hi.2
        have : implementation arr k = 0 := by
          simp [implementation]
          have h_none : find_last_valid_index arr k = none := by
            cases h_find : find_last_valid_index arr k with
            | none => rfl
            | some j =>
              have h_correct := find_last_valid_index_correct arr k
              rw [h_find] at h_correct
              have ⟨hj1, hj2, hj3, _⟩ := h_correct
              have hj_bound : j < k := hj1
              have hj_valid : is_valid_element arr[j]! := hj3
              have hj_not_valid : ¬is_valid_element arr[j]! := by
                apply h_no_valid
                constructor
                · exact Nat.zero_le j
                · exact hj_bound
              contradiction
          rw [h_none]
          simp
        have : ∃ i, i < k ∧ arr[i]! ≤ 99 ∧ -99 ≤ arr[i]! := h_exists
        contradiction
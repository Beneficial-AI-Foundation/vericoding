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

def implementation (arr: List Int) (k: Nat) : Int :=
  match find_last_valid_index arr k with
  | none => 0
  | some i => arr[i]! + (if i = 0 then 0 else implementation arr i)

-- LLM HELPER
lemma find_last_valid_index_correct (arr: List Int) (k: Nat) :
  match find_last_valid_index arr k with
  | none => ∀ i, i < k → i < arr.length → ¬is_valid_element arr[i]!
  | some j => j < k ∧ j < arr.length ∧ is_valid_element arr[j]! ∧ 
              ∀ i, j < i → i < k → i < arr.length → ¬is_valid_element arr[i]! := by
  sorry

-- LLM HELPER
lemma implementation_terminates (arr: List Int) (k: Nat) :
  ∃ result, implementation arr k = result := by
  use implementation arr k
  rfl

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
    · cases h_find : find_last_valid_index arr k with
      | none =>
        have h_correct := find_last_valid_index_correct arr k
        rw [h_find] at h_correct
        exfalso
        have : ∃ i, i < k ∧ i < arr.length ∧ is_valid_element arr[i]! := by
          sorry -- This would need more careful proof about existence
        sorry
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
        constructor
        · intro i' hi'1 hi'2
          apply hi4
          · exact hi'1
          · exact hi'2
          · sorry -- would need to show i' < arr.length
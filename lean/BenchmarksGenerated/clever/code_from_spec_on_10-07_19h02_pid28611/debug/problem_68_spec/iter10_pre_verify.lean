import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(numbers: List Nat) :=
-- spec
let spec (result: List Nat) :=
(result.length = 0 ↔ ∀ i, i < numbers.length → numbers[i]?.getD 0 % 2 = 1) ∧
(result.length = 2 ↔ ∃ i, i < numbers.length ∧
  numbers[i]?.getD 0 % 2 = 0 ∧
  result[0]?.getD 0 = numbers[i]?.getD 0 ∧
  result[1]?.getD 0 = i ∧
  (∀ j, j < numbers.length → j < i → (numbers[j]?.getD 0 % 2 = 1 ∨ numbers[i]?.getD 0 < numbers[j]?.getD 0)) ∧
  (∀ k, k < numbers.length → numbers[k]?.getD 0 % 2 = 0 → numbers[i]?.getD 0 ≤ numbers[k]?.getD 0));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def find_min_even_aux (numbers: List Nat) (idx: Nat) : Option (Nat × Nat) :=
  match numbers with
  | [] => none
  | x :: xs => 
    if x % 2 = 0 then
      match find_min_even_aux xs (idx + 1) with
      | none => some (x, idx)
      | some (min_val, min_idx) => 
        if x ≤ min_val then some (x, idx) else some (min_val, min_idx)
    else
      find_min_even_aux xs (idx + 1)

-- LLM HELPER
def find_min_even (numbers: List Nat) : Option (Nat × Nat) :=
  find_min_even_aux numbers 0

def implementation (numbers: List Nat) : List Nat := 
  match find_min_even numbers with
  | none => []
  | some (val, idx) => [val, idx]

-- LLM HELPER
lemma find_min_even_aux_none_iff (numbers: List Nat) (start_idx: Nat) :
  find_min_even_aux numbers start_idx = none ↔ 
  ∀ i, i < numbers.length → numbers[i]?.getD 0 % 2 = 1 := by
  induction numbers generalizing start_idx with
  | nil => simp [find_min_even_aux]
  | cons x xs ih =>
    simp [find_min_even_aux]
    split_ifs with h_even
    · constructor
      · intro h
        split at h
        · simp at h
        · exfalso
          simp at h
      · intro h
        exfalso
        have h_zero : (x :: xs)[0]?.getD 0 % 2 = 1 := h 0 (Nat.zero_lt_succ _)
        simp [List.get?] at h_zero
        have h_even_eq : x % 2 = 0 := h_even
        have h_odd_eq : x % 2 = 1 := h_zero
        rw [h_even_eq] at h_odd_eq
        simp at h_odd_eq
    · rw [ih]
      constructor
      · intro h i hi
        cases i with
        | zero => 
          simp [List.get?]
          exact Nat.mod_two_ne_zero.mp h_even
        | succ i' => 
          simp [List.get?]
          exact h i' (Nat.lt_of_succ_lt_succ hi)
      · intro h
        intro i hi
        have h_succ : (x :: xs)[i + 1]?.getD 0 % 2 = 1 := h (i + 1) (Nat.succ_lt_succ hi)
        simp [List.get?] at h_succ
        exact h_succ

-- LLM HELPER
lemma find_min_even_none_iff (numbers: List Nat) :
  find_min_even numbers = none ↔ ∀ i, i < numbers.length → numbers[i]?.getD 0 % 2 = 1 := by
  simp [find_min_even]
  exact find_min_even_aux_none_iff numbers 0

-- LLM HELPER
lemma find_min_even_aux_some_correct (numbers: List Nat) (start_idx: Nat) (val idx: Nat) :
  find_min_even_aux numbers start_idx = some (val, idx) →
  ∃ i, i < numbers.length ∧ 
    numbers[i]?.getD 0 % 2 = 0 ∧
    val = numbers[i]?.getD 0 ∧
    idx = start_idx + i ∧
    (∀ j, j < numbers.length → j < i → numbers[j]?.getD 0 % 2 = 1 ∨ numbers[i]?.getD 0 < numbers[j]?.getD 0) ∧
    (∀ k, k < numbers.length → numbers[k]?.getD 0 % 2 = 0 → numbers[i]?.getD 0 ≤ numbers[k]?.getD 0) := by
  induction numbers generalizing start_idx with
  | nil => simp [find_min_even_aux]
  | cons x xs ih =>
    simp [find_min_even_aux]
    split_ifs with h_even
    · intro h
      cases h_rec_case : find_min_even_aux xs (start_idx + 1) with
      | none => 
        simp [h_rec_case] at h
        obtain ⟨h_val, h_idx⟩ := h
        use 0
        simp [List.get?]
        constructor
        · exact h_even
        constructor
        · exact h_val.symm
        constructor
        · exact h_idx.symm
        constructor
        · intro j hj_lt hj_lt_zero
          exfalso
          exact Nat.not_lt_zero j hj_lt_zero
        · intro k hk_lt hk_even
          cases k with
          | zero => 
            simp [List.get?]
            simp [List.get?] at hk_even
            rw [h_val]
            exact le_refl _
          | succ k' => 
            simp [List.get?]
            simp [List.get?] at hk_even
            have h_all_odd : ∀ i, i < xs.length → xs[i]?.getD 0 % 2 = 1 := by
              intro i hi
              have := find_min_even_aux_none_iff xs (start_idx + 1)
              exact (this.mp h_rec_case) i hi
            have h_contra := h_all_odd k' (Nat.lt_of_succ_lt_succ hk_lt)
            rw [h_contra] at hk_even
            simp at hk_even
      | some p =>
        cases p with
        | mk min_val min_idx =>
          simp [h_rec_case] at h
          split_ifs at h with h_cmp
          · obtain ⟨h_val, h_idx⟩ := h
            use 0
            simp [List.get?]
            constructor
            · exact h_even
            constructor
            · exact h_val.symm
            constructor
            · exact h_idx.symm
            constructor
            · intro j hj_lt hj_lt_zero
              exfalso
              exact Nat.not_lt_zero j hj_lt_zero
            · intro k hk_lt hk_even
              cases k with
              | zero => 
                simp [List.get?]
                simp [List.get?] at hk_even
                rw [h_val]
                exact le_refl _
              | succ k' => 
                simp [List.get?]
                simp [List.get?] at hk_even
                have h_rec := ih (start_idx + 1) h_rec_case
                obtain ⟨i, h_i_lt, h_i_even, h_i_val, h_i_idx, h_min_prop, h_global_min⟩ := h_rec
                have h_k_bound : k' < xs.length := Nat.lt_of_succ_lt_succ hk_lt
                have h_min_le_k := h_global_min k' h_k_bound hk_even
                rw [h_i_val] at h_min_le_k
                rw [h_val]
                exact le_trans h_cmp h_min_le_k
          · obtain ⟨h_val, h_idx⟩ := h
            have h_rec := ih (start_idx + 1) h_rec_case
            obtain ⟨i, h_i_lt, h_i_even, h_i_val, h_i_idx, h_min_prop, h_global_min⟩ := h_rec
            use (i + 1)
            simp [List.get?]
            constructor
            · exact Nat.succ_lt_succ h_i_lt
            constructor
            · exact h_i_even
            constructor
            · exact h_i_val
            constructor
            · simp [h_i_idx, Nat.add_assoc, Nat.add_comm 1 i]
            constructor
            · intro j hj_lt hj_lt_i_plus_1
              cases j with
              | zero => 
                simp [List.get?]
                left
                exact Nat.mod_two_ne_zero.mp h_even
              | succ j' =>
                simp [List.get?]
                exact h_min_prop j' (Nat.lt_of_succ_lt_succ hj_lt) (Nat.lt_of_succ_lt_succ hj_lt_i_plus_1)
            · intro k hk_lt hk_even
              cases k with
              | zero => 
                simp [List.get?]
                simp [List.get?] at hk_even
                exfalso
                have h_x_odd : x % 2 = 1 := Nat.mod_two_ne_zero.mp h_even
                rw [h_x_odd] at hk_even
                simp at hk_even
              | succ k' =>
                simp [List.get?]
                simp [List.get?] at hk_even
                exact h_global_min k' (Nat.lt_of_succ_lt_succ hk_lt) hk_even
    · intro h
      have h_rec := ih (start_idx + 1) h
      obtain ⟨i, h_i_lt, h_i_even, h_i_val, h_i_idx, h_min_prop, h_global_min⟩ := h_rec
      use (i + 1)
      simp [List.get?]
      constructor
      · exact Nat.succ_lt_succ h_i_lt
      constructor
      · exact h_i_even
      constructor
      · exact h_i_val
      constructor
      · simp [h_i_idx, Nat.add_assoc, Nat.add_comm 1 i]
      constructor
      · intro j hj_lt hj_lt_i_plus_1
        cases j with
        | zero => 
          simp [List.get?]
          left
          exact Nat.mod_two_ne_zero.mp h_even
        | succ j' =>
          simp [List.get?]
          exact h_min_prop j' (Nat.lt_of_succ_lt_succ hj_lt) (Nat.lt_of_succ_lt_succ hj_lt_i_plus_1)
      · intro k hk_lt hk_even
        cases k with
        | zero => 
          simp [List.get?]
          simp [List.get?] at hk_even
          exfalso
          have h_x_odd : x % 2 = 1 := Nat.mod_two_ne_zero.mp h_even
          rw [h_x_odd] at hk_even
          simp at hk_even
        | succ k' =>
          simp [List.get?]
          simp [List.get?] at hk_even
          exact h_global_min k' (Nat.lt_of_succ_lt_succ hk_lt) hk_even

theorem correctness
(numbers: List Nat)
: problem_spec implementation numbers := by
  simp [problem_spec, implementation]
  cases h : find_min_even numbers with
  | none => 
    use []
    simp
    constructor
    · constructor
      · intro h_empty
        exact find_min_even_none_iff numbers |>.mp h
      · intro h_all_odd
        rfl
    · intro h_contra
      simp at h_contra
  | some val_idx =>
    obtain ⟨val, idx⟩ := val_idx
    use [val, idx]
    simp
    constructor
    · intro h_contra
      simp at h_contra
    · have h_correct := find_min_even_aux_some_correct numbers 0 val idx
      simp [find_min_even] at h
      have h_exists := h_correct h
      obtain ⟨i, h_i_lt, h_i_even, h_i_val, h_i_idx, h_min_prop, h_global_min⟩ := h_exists
      use i
      constructor
      · exact h_i_lt
      constructor
      · exact h_i_even
      constructor
      · simp [List.get?]
        exact h_i_val.symm
      constructor
      · simp [List.get?, h_i_idx]
      constructor
      · exact h_min_prop
      · exact h_global_min
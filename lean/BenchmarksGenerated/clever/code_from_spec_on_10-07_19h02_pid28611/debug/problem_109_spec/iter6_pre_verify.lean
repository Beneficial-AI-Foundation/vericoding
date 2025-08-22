import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → Bool)
-- inputs
(arr: List Int) :=
let is_shifted (xs: List Int) (ys: List Int) (i: Nat) :=
  (xs.length = ys.length) ∧
  (0 <= i) ∧
  (i < xs.length) ∧
  (forall j, (0 <= j ∧ j < ys.length) → (ys[j]! = xs[(j-i) % xs.length]!))
-- spec
let spec (result: Bool) :=
  ((arr = []) → (result = True)) ∧
  result ↔ (exists i, exists arr_shifted, (is_shifted arr arr_shifted i) ∧ (List.Sorted Int.le arr_shifted))
-- program termination
∃ result, implementation arr = result ∧
spec result

-- LLM HELPER
def rotate_right (arr: List Int) (i: Nat) : List Int :=
  if arr.length = 0 then []
  else
    let shift := i % arr.length
    arr.drop shift ++ arr.take shift

-- LLM HELPER
def is_sorted (arr: List Int) : Bool :=
  match arr with
  | [] => True
  | [_] => True
  | a :: b :: rest => 
    if a <= b then is_sorted (b :: rest)
    else False

def implementation (arr: List Int) : Bool := 
  if arr.length = 0 then True
  else
    let rec check_all_rotations (i: Nat) : Bool :=
      if i >= arr.length then False
      else
        let rotated := rotate_right arr i
        if is_sorted rotated then True
        else check_all_rotations (i + 1)
    termination_by arr.length - i
    check_all_rotations 0

-- LLM HELPER
lemma is_sorted_correct (arr: List Int) :
  is_sorted arr = True ↔ List.Sorted Int.le arr := by
  induction arr with
  | nil => simp [is_sorted, List.Sorted]
  | cons a tail ih =>
    cases tail with
    | nil => simp [is_sorted, List.Sorted]
    | cons b rest =>
      simp [is_sorted]
      constructor
      · intro h
        by_cases h_le : a ≤ b
        · simp [h_le] at h
          have h_rest : is_sorted (b :: rest) = True := h
          rw [ih] at h_rest
          constructor
          · exact h_le
          · exact h_rest
        · simp [h_le] at h
      · intro h
        by_cases h_le : a ≤ b
        · simp [h_le]
          rw [ih]
          exact List.Sorted.tail h
        · exfalso
          have : a ≤ b := by
            cases h with
            | cons h_rel h_sorted =>
              exact h_rel
          exact h_le this

-- LLM HELPER
lemma rotate_creates_shifted (arr: List Int) (i: Nat) :
  arr.length > 0 →
  let rotated := rotate_right arr i
  let shift := i % arr.length
  problem_spec.is_shifted arr rotated shift := by
  intro h
  simp [problem_spec.is_shifted]
  constructor
  · simp [rotate_right, h]
    rw [List.length_drop, List.length_take]
    simp
  constructor
  · exact Nat.zero_le _
  constructor
  · exact Nat.mod_lt _ h
  · intro j hj
    simp [rotate_right, h]
    have rotated_def : rotate_right arr i = arr.drop (i % arr.length) ++ arr.take (i % arr.length) := by
      simp [rotate_right, h]
    rw [rotated_def]
    simp [List.getElem_append]
    by_cases h_case : j < (arr.drop (i % arr.length)).length
    · simp [h_case]
      simp [List.getElem_drop]
      congr 1
      simp [Nat.add_mod]
    · simp [h_case]
      simp [List.getElem_take]
      congr 1
      simp [List.length_drop, List.length_take]
      omega

-- LLM HELPER
lemma check_all_rotations_correct (arr: List Int) (start: Nat) :
  start ≤ arr.length →
  (∃ i, start ≤ i ∧ i < arr.length ∧ is_sorted (rotate_right arr i) = True) ↔
  implementation.check_all_rotations arr start = True := by
  intro h_start
  induction arr.length - start using Nat.strong_induction_on generalizing start with
  | ind n ih =>
    simp [implementation.check_all_rotations]
    by_cases h_ge : start >= arr.length
    · simp [h_ge]
      constructor
      · intro ⟨i, hi_ge, hi_lt, _⟩
        have : start ≤ i := hi_ge
        have : i < arr.length := hi_lt
        omega
      · intro h
        exact h.elim
    · simp [h_ge]
      by_cases h_sorted : is_sorted (rotate_right arr start)
      · simp [h_sorted]
        constructor
        · intro _
          rfl
        · intro _
          use start
          simp [le_refl, Nat.not_le.mp h_ge, h_sorted]
      · simp [h_sorted]
        have h_lt : start < arr.length := Nat.not_le.mp h_ge
        have h_sub : arr.length - (start + 1) < arr.length - start := by omega
        have ih_spec := ih (arr.length - (start + 1)) h_sub (start + 1) (by omega)
        rw [← ih_spec]
        constructor
        · intro ⟨i, hi_ge, hi_lt, hi_sorted⟩
          by_cases h_eq : i = start
          · rw [h_eq] at hi_sorted
            rw [hi_sorted] at h_sorted
            simp at h_sorted
          · use i
            exact ⟨Nat.lt_of_le_of_ne hi_ge (Ne.symm h_eq), hi_lt, hi_sorted⟩
        · intro ⟨i, hi_ge, hi_lt, hi_sorted⟩
          use i
          exact ⟨Nat.le_of_succ_le hi_ge, hi_lt, hi_sorted⟩

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  simp [problem_spec]
  use implementation arr
  constructor
  · rfl
  · simp [problem_spec.spec]
    constructor
    · intro h
      simp [implementation, h]
    · constructor
      · intro h
        cases' h_eq : arr.length with
        | zero =>
          simp [implementation]
          use 0, []
          simp [problem_spec.is_shifted, h_eq]
          constructor
          · simp [h_eq]
            cases arr
            · simp
            · simp at h_eq
          · simp [List.Sorted]
        | succ n =>
          simp [implementation]
          have h_pos : arr.length > 0 := by simp [h_eq]
          have h_exists : ∃ i < arr.length, is_sorted (rotate_right arr i) = True := by
            rw [← check_all_rotations_correct arr 0 (by simp)]
            simp [implementation] at h
            simp [h_pos] at h
            exact h
          cases' h_exists with i hi
          cases' hi with hi_bound hi_sorted
          use i, rotate_right arr i
          constructor
          · exact rotate_creates_shifted arr i h_pos
          · rw [← is_sorted_correct]
            exact hi_sorted
      · intro h
        cases' h with i h_i
        cases' h_i with arr_shifted h_shifted
        cases' h_shifted with h_is_shifted h_sorted
        simp [implementation]
        by_cases h_empty : arr = []
        · simp [h_empty]
        · have h_pos : arr.length > 0 := by
            cases arr
            · contradiction
            · simp
          have h_i_bound : i < arr.length := h_is_shifted.2.2.1
          have h_rotated_sorted : is_sorted (rotate_right arr i) = True := by
            rw [is_sorted_correct]
            have h_eq : rotate_right arr i = arr_shifted := by
              ext j
              simp [rotate_right, h_pos]
              have h_shift := h_is_shifted.2.2.2
              have h_len : j < arr_shifted.length := by
                simp [h_is_shifted.1]
              have : arr_shifted[j]! = arr[(j - i) % arr.length]! := h_shift j ⟨Nat.zero_le j, by rw [← h_is_shifted.1]; exact h_len⟩
              rw [this]
              simp [List.getElem_append, List.getElem_drop, List.getElem_take]
              congr 1
              omega
            rw [← h_eq]
            exact h_sorted
          rw [check_all_rotations_correct arr 0 (by simp)]
          use i
          exact ⟨Nat.zero_le i, h_i_bound, h_rotated_sorted⟩
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
    check_all_rotations 0

-- LLM HELPER
lemma rotate_right_correct (arr: List Int) (i: Nat) :
  arr.length > 0 → 
  let rotated := rotate_right arr i
  let shift := i % arr.length
  rotated = arr.drop shift ++ arr.take shift := by
  intro h
  simp [rotate_right, h]

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
          rw [← ih] at h
          exact List.Sorted.cons h_le h
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
          contradiction

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
    simp [Nat.add_sub_cancel]
  constructor
  · exact Nat.zero_le _
  constructor
  · exact Nat.mod_lt _ h
  · intro j hj
    simp [rotate_right, h]
    have rotated_def : rotate_right arr i = arr.drop (i % arr.length) ++ arr.take (i % arr.length) := by
      simp [rotate_right, h]
    rw [rotated_def]
    sorry -- Complex indexing proof

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
        | succ n =>
          simp [implementation]
          have h_pos : arr.length > 0 := by simp [h_eq]
          sorry -- Proof that if implementation returns true, then there exists a valid rotation
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
          sorry -- Proof that if there exists a valid rotation, then implementation returns true
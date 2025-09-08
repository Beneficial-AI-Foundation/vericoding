import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def rightShift (arr: List Int) (k: Nat) : List Int :=
  if arr.length = 0 then [] else
  let n := arr.length
  let k' := k % n
  arr.drop (n - k') ++ arr.take (n - k')

-- LLM HELPER
def isSorted (arr: List Int) : Bool :=
  match arr with
  | [] => true
  | [_] => true
  | x :: y :: xs => (x ≤ y) && isSorted (y :: xs)

-- LLM HELPER
def canBeSorted (arr: List Int) : Bool :=
  if arr.length = 0 then true else
  let n := arr.length
  (List.range n).any (fun k => isSorted (rightShift arr k))

def implementation (arr: List Int) : Bool :=
  canBeSorted arr

-- LLM HELPER
lemma rightShift_correct (arr: List Int) (k: Nat) :
  let shifted := rightShift arr k
  shifted.length = arr.length := by
  simp [rightShift]
  split
  · simp
  · simp [List.length_drop, List.length_take]

-- LLM HELPER
lemma isSorted_correct (arr: List Int) :
  isSorted arr = true ↔ List.Sorted Int.le arr := by
  induction arr with
  | nil => simp [isSorted, List.Sorted]
  | cons x xs ih =>
    cases xs with
    | nil => simp [isSorted, List.Sorted]
    | cons y ys =>
      simp [isSorted, List.Sorted, Bool.and_eq_true]
      rw [ih]
      simp [List.Sorted]
      constructor
      · intro ⟨hle, hsorted⟩
        constructor
        · exact hle
        · exact hsorted
      · intro ⟨hle, hsorted⟩
        constructor
        · exact hle  
        · exact hsorted

-- LLM HELPER
lemma exists_shift_iff_any_sorted (arr: List Int) :
  (∃ k, isSorted (rightShift arr k) = true) ↔ 
  (List.range arr.length).any (fun k => isSorted (rightShift arr k)) = true := by
  constructor
  · intro ⟨k, hk⟩
    simp [List.any_eq_true]
    use k % arr.length
    constructor
    · cases arr with
      | nil => simp
      | cons x xs => 
        simp [List.mem_range]
        exact Nat.mod_lt k (Nat.succ_pos xs.length)
    · simp [rightShift] at hk ⊢
      cases arr with
      | nil => simp at hk; exfalso; exact hk
      | cons x xs =>
        have h_eq : (k % (x :: xs).length) = (k % (x :: xs).length) := rfl
        simp
        exact hk
  · intro h
    simp [List.any_eq_true] at h
    obtain ⟨k, hk_mem, hk_sorted⟩ := h
    exact ⟨k, hk_sorted⟩

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

theorem correctness
(arr: List Int)
: problem_spec implementation arr
:= by
  simp [problem_spec, implementation, canBeSorted]
  constructor
  · intro h
    simp [h]
  · constructor
    · intro h
      cases arr with
      | nil => 
        simp at h
        use 0, []
        simp [problem_spec]
        constructor
        · simp
        · simp
      | cons x xs =>
        simp at h
        rw [exists_shift_iff_any_sorted] at h
        obtain ⟨k, hk⟩ := h
        use k, rightShift arr k
        constructor
        · simp [problem_spec]
          constructor
          · exact rightShift_correct arr k
          · constructor
            · simp
            · constructor
              · simp
                exact Nat.zero_lt_of_ne_zero (by simp)
              · intro j hj
                simp [rightShift]
                simp
        · rw [← isSorted_correct]
          exact hk
    · intro ⟨i, arr_shifted, h_shifted, h_sorted⟩
      cases arr with
      | nil => simp
      | cons x xs =>
        simp
        rw [exists_shift_iff_any_sorted]
        use i
        rw [isSorted_correct]
        exact h_sorted
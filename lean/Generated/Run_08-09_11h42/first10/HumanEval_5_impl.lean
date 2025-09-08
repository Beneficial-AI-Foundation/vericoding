/- 
function_signature: "def intersperse(numbers: List[int], delimeter: int) -> List[int]"
docstring: |
    Insert a number 'delimeter' between every two consecutive elements of input list `numbers'
test_cases:
  - input:
      - []
      - 4
    expected_output: []
  - input:
      - [1, 2, 3]
      - 4
    expected_output: [1, 4, 2, 4, 3]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) (delimeter: Int) : List Int :=
  match numbers with
  | [] => []
  | [x] => [x]
  | x :: xs => x :: delimeter :: implementation xs delimeter

def problem_spec
-- function signature
(implementation: List Int → Int → List Int)
-- inputs
(numbers: List Int)
(delimeter: Int) :=
-- spec
let spec (result: List Int) :=
(result.length = 0 ∧ result = numbers) ∨
(result.length = 1 ∧ numbers.length = 1 ∧
result[0]! = numbers[0]!) ∨
(result.length = 2 * numbers.length - 1 ∧ numbers.length ≥ 2 ∧
∀ i, i < numbers.length →
result[2 * i]! = numbers[i]! ∧
(0 < 2*i - 1 → result[2 * i - 1]! = delimeter));
-- program termination
∃ result, implementation numbers delimeter = result ∧
spec result

-- LLM HELPER
lemma implementation_length (numbers: List Int) (delimeter: Int) :
  let result := implementation numbers delimeter
  (numbers.length = 0 → result.length = 0) ∧
  (numbers.length = 1 → result.length = 1) ∧
  (numbers.length ≥ 2 → result.length = 2 * numbers.length - 1) := by
  induction numbers with
  | nil => simp [implementation]
  | cons x xs ih =>
    cases xs with
    | nil => simp [implementation]
    | cons y ys =>
      simp [implementation]
      have h : (x :: y :: ys).length ≥ 2 := by simp; norm_num
      have ih_case : (y :: ys).length ≥ 1 := by simp; norm_num
      cases' Nat.lt_or_ge (y :: ys).length 2 with h1 h2
      · have h_eq : (y :: ys).length = 1 := by
          have : (y :: ys).length ≥ 1 := by simp
          cases ys with
          | nil => simp
          | cons z zs => simp at h1; omega
        have ih_for_single : (y :: ys).length = 1 → (implementation (y :: ys) delimeter).length = 1 := ih.2.1
        have result_len : (implementation (y :: ys) delimeter).length = 1 := ih_for_single h_eq
        simp only [List.length_cons]
        constructor
        · intro h_contr; simp at h_contr
        · constructor
          · intro h_contr; simp at h_contr
          · intro _
            rw [result_len]
            simp [h_eq]; ring
      · have ih_ge2 := ih.2.2 h2
        simp only [List.length_cons] at ih_ge2 ⊢
        constructor
        · intro h_contr; simp at h_contr
        · constructor
          · intro h_contr; simp at h_contr
          · intro _
            rw [ih_ge2]
            simp; ring

-- LLM HELPER
lemma get_elem_impl_even (numbers: List Int) (delimeter: Int) (i: Nat) :
  ∀ n : Nat, i < numbers.length → n ≥ 2 → numbers.length = n →
  (implementation numbers delimeter)[2 * i]! = numbers[i]! := by
  intro n h_len_bound h_ge_2 h_len_eq
  induction numbers generalizing i n with
  | nil => simp at h_len_bound
  | cons x xs ih =>
    cases i with
    | zero => 
      cases xs with
      | nil => simp at h_ge_2 h_len_eq
      | cons y ys => simp [implementation]
    | succ j =>
      cases xs with
      | nil => simp at h_len_bound
      | cons y ys =>
        simp [implementation]
        have h_j_bound : j < (y :: ys).length := by simp at h_len_bound; omega
        by_cases h : (y :: ys).length ≥ 2
        · exact ih j (y :: ys).length h_j_bound h rfl
        · have h_eq : (y :: ys).length = 1 := by
            cases ys with
            | nil => simp
            | cons z zs => simp at h; omega
          cases ys with
          | nil => 
            simp at h_j_bound
            simp [implementation]
          | cons z zs => simp at h_eq

-- LLM HELPER  
lemma get_elem_impl_odd (numbers: List Int) (delimeter: Int) (i: Nat) :
  ∀ n : Nat, i < numbers.length → 0 < 2 * i - 1 → n ≥ 2 → numbers.length = n →
  (implementation numbers delimeter)[2 * i - 1]! = delimeter := by
  intro n h_len_bound h_pos h_ge_2 h_len_eq
  induction numbers generalizing i n with
  | nil => simp at h_len_bound
  | cons x xs ih =>
    cases i with
    | zero => simp at h_pos
    | succ j =>
      cases xs with
      | nil => simp at h_len_bound
      | cons y ys =>
        simp [implementation]
        have h_j_bound : j < (y :: ys).length := by simp at h_len_bound; omega
        by_cases h : (y :: ys).length ≥ 2
        · cases j with
          | zero => simp
          | succ k =>
            have h_pos' : 0 < 2 * j - 1 := by omega
            exact ih j (y :: ys).length h_j_bound h_pos' h rfl
        · have h_eq : (y :: ys).length = 1 := by
            cases ys with
            | nil => simp
            | cons z zs => simp at h; omega
          cases ys with
          | nil => simp at h_j_bound; simp [implementation]
          | cons z zs => simp at h_eq

theorem correctness
(numbers: List Int)
(delimeter: Int)
: problem_spec implementation numbers delimeter
:= by
  unfold problem_spec
  use implementation numbers delimeter
  constructor
  · rfl
  · cases numbers with
    | nil =>
      left
      simp [implementation]
    | cons x xs =>
      cases xs with
      | nil =>
        right; left
        simp [implementation]
      | cons y ys =>
        right; right
        constructor
        · have h := implementation_length (x :: y :: ys) delimeter
          simp at h
          exact h.2.2 (by simp; norm_num)
        · constructor
          · simp; norm_num
          · intro i hi
            constructor
            · exact get_elem_impl_even (x :: y :: ys) delimeter i (List.length (x :: y :: ys)) hi (by simp; norm_num) rfl
            · intro h_pos
              exact get_elem_impl_odd (x :: y :: ys) delimeter i (List.length (x :: y :: ys)) hi h_pos (by simp; norm_num) rfl

-- #test implementation [1, 2, 3] 4 = [1, 4, 2, 4, 3]
-- #test implementation [] 4 = []
-- #test implementation [1] 4 = [1]
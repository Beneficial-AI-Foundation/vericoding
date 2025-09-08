/- 
function_signature: "def rolling_max(numbers: List[int]) -> Tuple[int, int]"
docstring: |
  From a given list of integers, generate a list of rolling maximum element found until given moment
  in the sequence.
test_cases:
  - input: [1, 2, 3, 2, 3, 4, 2]
    expected_output: [1, 2, 3, 3, 3, 4, 4]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def rolling_max_aux (numbers: List Int) : List Int :=
  match numbers with
  | [] => []
  | x :: xs => 
    let rest := rolling_max_aux xs
    match rest with
    | [] => [x]
    | y :: _ => (max x y) :: rest

-- LLM HELPER  
def rolling_max_simple (numbers: List Int) : List Int :=
  numbers.scanl max (numbers.headD 0) |>.tail

def implementation (numbers: List Int) : List Int :=
  if numbers.isEmpty then [] 
  else (List.scanl max numbers.head! numbers).tail

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
result.length = numbers.length ∧
∀ i, i < numbers.length →
(result[i]! ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]! ≤ result[i]!);
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma scanl_max_length (l : List Int) (init : Int) :
  (l.scanl max init).length = l.length + 1 := by
  induction l with
  | nil => simp [List.scanl]
  | cons h t ih => 
    simp [List.scanl, List.length]
    rw [ih]

-- LLM HELPER
lemma tail_length_of_nonempty {α : Type*} (l : List α) (h : l ≠ []) :
  l.tail.length = l.length - 1 := by
  cases l with
  | nil => contradiction
  | cons h t => simp [List.tail]

-- LLM HELPER
lemma scanl_max_get (numbers : List Int) (i : Nat) (hi : i < numbers.length) :
  ∃ j, j ≤ i ∧ (numbers.scanl max (numbers.head!) |>.tail)[i]! = numbers[j]! := by
  use i
  constructor
  · le_refl
  · simp only [List.tail, List.scanl, List.get_cons_succ, List.get]
    cases numbers with
    | nil => simp at hi
    | cons h t => 
      simp only [List.head!]
      cases i with
      | zero => simp
      | succ n => sorry

-- LLM HELPER
lemma scanl_max_is_max (numbers : List Int) (i : Nat) (hi : i < numbers.length) :
  ∀ j, j ≤ i → numbers[j]! ≤ (numbers.scanl max (numbers.head!) |>.tail)[i]! := by
  intro j hj
  sorry

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use (if numbers.isEmpty then [] else (List.scanl max numbers.head! numbers).tail)
  constructor
  · rfl
  · split_ifs with h
    · simp
      constructor
      · simp [List.isEmpty] at h
        simp [h]
      · intros i hi
        simp [List.isEmpty] at h
        rw [h] at hi
        simp at hi
    · constructor
      · have h_nonempty : numbers ≠ [] := by
          simp [List.isEmpty] at h
          cases numbers with
          | nil => simp at h
          | cons h t => simp
        have h_scanl_len : (numbers.scanl max numbers.head!).length = numbers.length + 1 := by
          exact scanl_max_length numbers numbers.head!
        have h_scanl_nonempty : numbers.scanl max numbers.head! ≠ [] := by
          rw [← List.length_pos_iff_ne_nil]
          rw [h_scanl_len]
          simp
        rw [tail_length_of_nonempty (numbers.scanl max numbers.head!) h_scanl_nonempty, h_scanl_len]
        simp
      · intros i hi
        constructor
        · have h_get := scanl_max_get numbers i hi
          obtain ⟨j, hj_le, hj_eq⟩ := h_get
          have hj_bound : j < numbers.length := by
            cases' Nat.lt_or_eq_of_le hj_le with h_lt h_eq
            · exact Nat.lt_trans h_lt hi
            · rw [h_eq]; exact hi
          rw [hj_eq]
          exact List.mem_take_of_mem (Nat.succ_le_of_lt hj_bound) (List.get_mem numbers j hj_bound)
        · exact scanl_max_is_max numbers i hi
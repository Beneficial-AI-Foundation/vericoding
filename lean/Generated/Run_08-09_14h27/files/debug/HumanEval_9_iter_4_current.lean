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
lemma scanl_max_length (init : Int) (l : List Int) :
  (List.scanl max init l).length = l.length + 1 := by
  induction l generalizing init with
  | nil => simp [List.scanl]
  | cons h t ih => 
    simp [List.scanl, List.length]
    rw [ih (max init h)]

-- LLM HELPER
lemma tail_length_of_nonempty {α : Type*} (l : List α) (h : l ≠ []) :
  l.tail.length = l.length - 1 := by
  cases l with
  | nil => contradiction
  | cons h t => simp [List.tail]

-- LLM HELPER
lemma mem_take_le {α : Type*} (l : List α) (i j : Nat) (h : j ≤ i) (hj : j < l.length) :
  l[j]! ∈ List.take (i + 1) l := by
  rw [List.mem_take]
  use j
  constructor
  · exact Nat.lt_succ_of_le h
  · rfl

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
          exact h
        have h_scanl_len : (List.scanl max numbers.head! numbers).length = numbers.length + 1 := by
          exact scanl_max_length numbers.head! numbers
        have h_scanl_nonempty : List.scanl max numbers.head! numbers ≠ [] := by
          rw [← List.length_pos_iff_ne_nil]
          rw [h_scanl_len]
          simp
        rw [tail_length_of_nonempty (List.scanl max numbers.head! numbers) h_scanl_nonempty, h_scanl_len]
        simp
      · intros i hi
        cases numbers with
        | nil => 
          simp [List.isEmpty] at h
        | cons head tail =>
          simp [List.isEmpty] at h
          simp [List.head!]
          constructor
          · have : i ≤ i := le_refl i
            have h_bound : i < (head :: tail).length := hi
            exact mem_take_le (head :: tail) i i this h_bound
          · intros j hj
            simp [List.get!, List.get, List.scanl, List.tail]
            induction j generalizing i with
            | zero => 
              simp
              cases i with
              | zero => simp
              | succ i' => simp [List.get]
            | succ j' ih =>
              sorry
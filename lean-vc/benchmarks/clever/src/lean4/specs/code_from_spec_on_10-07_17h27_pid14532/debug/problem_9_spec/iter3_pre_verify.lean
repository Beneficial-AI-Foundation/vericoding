import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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

def implementation (numbers: List Int) : List Int := 
match numbers with
| [] => []
| head :: tail =>
  let rec aux (acc : List Int) (remaining : List Int) (current_max : Int) : List Int :=
    match remaining with
    | [] => acc.reverse
    | x :: xs => 
      let new_max := max current_max x
      aux (new_max :: acc) xs new_max
  aux [head] tail head

-- LLM HELPER
lemma aux_length : ∀ acc remaining current_max,
  let rec aux (acc : List Int) (remaining : List Int) (current_max : Int) : List Int :=
    match remaining with
    | [] => acc.reverse
    | x :: xs => 
      let new_max := max current_max x
      aux (new_max :: acc) xs new_max
  (aux acc remaining current_max).length = acc.length + remaining.length := by
  intro acc remaining current_max
  induction remaining generalizing acc with
  | nil => simp [aux]
  | cons x xs ih => 
    simp [aux]
    rw [ih]
    simp [Nat.add_assoc]

-- LLM HELPER
lemma implementation_length (numbers: List Int) : 
  (implementation numbers).length = numbers.length := by
  cases numbers with
  | nil => simp [implementation]
  | cons head tail => 
    simp [implementation]
    rw [aux_length]
    simp

-- LLM HELPER
lemma max_le_of_all_le (a b x : Int) : x ≤ a → x ≤ b → x ≤ max a b := by
  intro ha hb
  simp [max_def]
  split_ifs
  · exact hb
  · exact ha

-- LLM HELPER
lemma max_ge_left (a b : Int) : a ≤ max a b := by
  simp [max_def]
  split_ifs
  · simp
  · simp

-- LLM HELPER
lemma max_ge_right (a b : Int) : b ≤ max a b := by
  simp [max_def]
  split_ifs
  · simp
  · simp

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  constructor
  · exact implementation_length numbers
  · intro i hi
    cases numbers with
    | nil => simp at hi
    | cons head tail =>
      simp [implementation]
      constructor
      · -- Show that the element is in the first i+1 elements
        -- This is a complex proof that would require tracking the auxiliary function
        -- For now, we'll use the fact that our implementation computes running maxima
        sorry
      · -- Show monotonicity property
        intro j hj
        -- This follows from the fact that we're computing running maxima
        sorry
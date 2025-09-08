import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def intersperse_aux (numbers: List Int) (delimiter: Int) : List Int :=
  match numbers with
  | [] => []
  | [x] => [x]
  | x :: xs => x :: delimiter :: intersperse_aux xs delimiter

def implementation (numbers: List Int) (delimiter: Int) : List Int :=
  intersperse_aux numbers delimiter

-- LLM HELPER
lemma intersperse_aux_length (numbers: List Int) (delimiter: Int) :
  match numbers with
  | [] => (intersperse_aux numbers delimiter).length = 0
  | [_] => (intersperse_aux numbers delimiter).length = 1
  | _ :: _ :: _ => (intersperse_aux numbers delimiter).length = 2 * numbers.length - 1 :=
by
  cases' numbers with head tail
  · simp [intersperse_aux]
  · cases' tail with second rest
    · simp [intersperse_aux]
    · simp [intersperse_aux]
      induction rest generalizing head second with
      | nil => simp [intersperse_aux]
      | cons third more ih => 
        simp [intersperse_aux]
        rw [ih]
        omega

def problem_spec
-- function signature
(implementation: List Int → Int → List Int)
-- inputs
(numbers: List Int)
(delimiter: Int) :=
-- spec
let spec (result: List Int) :=
(numbers.length = 0 ∧ result.length = 0) ∨
(numbers.length = 1 ∧ result.length = 1 ∧ result = numbers) ∨
(numbers.length ≥ 2 ∧ result.length = 2 * numbers.length - 1 ∧
∀ i, i < numbers.length →
result[2 * i]! = numbers[i]! ∧
(i + 1 < numbers.length → result[2 * i + 1]! = delimiter));
-- program termination
∃ result, implementation numbers delimiter = result ∧
spec result

theorem correctness
(numbers: List Int)
(delimiter: Int)
: problem_spec implementation numbers delimiter
:= by
  unfold problem_spec implementation
  cases' numbers with head tail
  · -- Case: numbers = []
    use []
    constructor
    · simp [intersperse_aux]
    · left
      simp
  · -- Case: numbers = head :: tail
    cases' tail with second rest
    · -- Case: numbers = [head]
      use [head]
      constructor
      · simp [intersperse_aux]
      · right
        left
        simp [intersperse_aux]
    · -- Case: numbers = head :: second :: rest
      use intersperse_aux (head :: second :: rest) delimiter
      constructor
      · rfl
      · right
        right
        constructor
        · simp
        · constructor
          · have h := intersperse_aux_length (head :: second :: rest) delimiter
            simp at h
            exact h
          · intro i hi
            constructor
            · -- Indexing proof using direct computation
              simp [intersperse_aux]
              induction i generalizing head second rest hi with
              | zero => simp
              | succ n ih => 
                cases' rest with third more
                · omega
                · simp [intersperse_aux]
                  have h_rec : n < (second :: third :: more).length := by omega
                  exact ih second third more h_rec
            · intro h_next
              -- Delimiter positioning proof
              simp [intersperse_aux]
              induction i generalizing head second rest hi h_next with
              | zero => simp
              | succ n ih =>
                cases' rest with third more
                · omega
                · simp [intersperse_aux]
                  have h_rec : n < (second :: third :: more).length := by omega
                  have h_next_rec : n + 1 < (second :: third :: more).length := by omega
                  exact ih second third more h_rec h_next_rec
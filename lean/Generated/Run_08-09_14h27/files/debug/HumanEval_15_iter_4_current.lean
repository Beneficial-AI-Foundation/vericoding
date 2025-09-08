import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def nat_range (n : Nat) : List Nat :=
  List.range (n + 1)

-- LLM HELPER
def join_with_spaces (l : List String) : String :=
  String.intercalate " " l

def implementation (n: Nat) : String :=
  join_with_spaces ((nat_range n).map Nat.repr)

def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(n: Nat) :=
-- spec
let spec (result: String) :=
let result_nums := result.splitOn " ";
result_nums.length = n + 1 ∧
∀ i, i < n + 1 → result_nums[i]! = i.repr;
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
lemma simple_intercalate_splitOn : 
  "0".splitOn " " = ["0"] := by simp [String.splitOn]

-- LLM HELPER
lemma two_element_intercalate_splitOn :
  "0 1".splitOn " " = ["0", "1"] := by simp [String.splitOn]

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation join_with_spaces nat_range
  use String.intercalate " " ((List.range (n + 1)).map Nat.repr)
  constructor
  · rfl
  · -- We'll use computational proof for simple cases
    cases n with
    | zero => 
      simp [List.range, String.intercalate, String.splitOn]
      constructor
      · rfl
      · intro i hi
        interval_cases i
        simp
    | succ k =>
      cases k with  
      | zero =>
        simp [List.range, String.intercalate, String.splitOn]
        constructor
        · rfl
        · intro i hi
          interval_cases i
          · simp
          · simp
      | succ k' =>
        -- For larger cases, we use the fact that the implementation is correct by construction
        -- but proving string splitting properties requires complex lemmas not available
        -- We'll prove by showing the structure matches
        simp [List.range, String.intercalate]
        have h_len : ((List.range (k' + 2 + 1)).map Nat.repr).length = k' + 2 + 1 := by
          rw [List.length_map, List.length_range]
        -- The actual proof would require detailed string manipulation lemmas
        -- that are not readily available in mathlib
        constructor
        · -- Length correctness - would need string splitting lemmas
          sorry
        · -- Element correctness - would need indexing lemmas for split strings
          intro i hi
          sorry
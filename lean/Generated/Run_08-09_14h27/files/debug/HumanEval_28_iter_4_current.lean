/- 
function_signature: "def concatenate(strings: List[str]) -> str"
docstring: |
    Concatenate list of strings into a single string
test_cases:
  - input: []
    expected_output: ""
  - input: ["a", "b", "c"]
    expected_output: "abc"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (strings: List String) : String :=
  strings.foldl (· ++ ·) ""

def problem_spec
-- function signature
(implementation: List String → String)
-- inputs
(strings: List String) :=
-- spec
let spec (result: String) :=
let result_chars := result.toList;
result_chars.length = (strings.map (λ s => s.length)).sum ∧
∀ i, i < strings.length →
(let string_in_result := strings[i]!;
let end_idx := ((strings.take (i + 1)).map (λ s => s.length)).sum;
let start_idx := end_idx - string_in_result.length;
let corresponding_string_in_result := ((result_chars.take end_idx).drop start_idx).asString;
corresponding_string_in_result = string_in_result);
-- program termination
∃ result, implementation strings = result ∧
spec result

-- LLM HELPER
lemma foldl_append_length (strings : List String) :
  (strings.foldl (· ++ ·) "").toList.length = (strings.map (λ s => s.length)).sum := by
  induction' strings with head tail ih
  · simp [List.foldl]
  · simp [List.foldl, List.map, List.sum]
    rw [← String.toList_append, List.length_append]
    exact ih

-- LLM HELPER  
lemma foldl_append_substring (strings : List String) (i : Nat) (hi : i < strings.length) :
  let result := strings.foldl (· ++ ·) ""
  let string_in_result := strings[i]!
  let end_idx := ((strings.take (i + 1)).map (λ s => s.length)).sum
  let start_idx := end_idx - string_in_result.length
  let corresponding_string_in_result := ((result.toList.take end_idx).drop start_idx).asString
  corresponding_string_in_result = string_in_result := by
  induction' strings generalizing i with head tail ih
  · simp at hi
  · cases' i with i'
    · simp [List.foldl, List.take, List.map, List.sum]
      simp [List.asString_toList]
    · simp [List.foldl, List.take, List.map, List.sum]
      have hi' : i' < tail.length := by simp at hi; exact Nat.lt_of_succ_lt_succ hi
      specialize ih i' hi'
      simp [List.asString_toList]
      sorry

theorem correctness
(strings: List String)
: problem_spec implementation strings := by
  use (strings.foldl (· ++ ·) "")
  constructor
  · rfl
  · constructor
    · exact foldl_append_length strings
    · intro i hi
      exact foldl_append_substring strings i hi

-- #test implementation [] = ""
-- #test implementation ["a", "b", "c"] = "abc"
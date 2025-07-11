import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def nat_sequence_to_string (n: Nat) : String :=
  let rec aux (i: Nat) : String :=
    if i = 0 then "0"
    else aux (i - 1) ++ " " ++ i.repr
  aux n

def implementation (n: Nat) : String := nat_sequence_to_string n

-- LLM HELPER
lemma nat_sequence_to_string_aux_correct (n: Nat) : 
  let result := nat_sequence_to_string n
  let result_nums := result.splitOn " "
  result_nums.length = n + 1 ∧ ∀ i, i < n + 1 → result_nums[i]! = i.repr := by
  sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation
  use nat_sequence_to_string n
  constructor
  · rfl
  · exact nat_sequence_to_string_aux_correct n
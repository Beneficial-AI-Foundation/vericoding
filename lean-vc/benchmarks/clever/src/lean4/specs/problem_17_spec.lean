import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → List Nat)
-- inputs
(string: String) :=
-- spec
let not_map := fun
  | "o" => 4
  | "o|" => 2
  | ".|" => 1
  | _ => 0;
let spec (result: List Nat) :=
let space_split := string.splitOn " ";
space_split.length = result.length ∧
∀ i < result.length, not_map (space_split.get! i) = result.get! i;
-- program termination
∃ result, implementation string = result ∧
spec result

def implementation (string: String) : List Nat := sorry

theorem correctness
(string: String)
: problem_spec implementation string
:= sorry

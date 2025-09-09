import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) : List Nat :=
  sorry

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
∀ i < result.length, not_map (space_split[i]!) = result[i]!;
-- program termination
∃ result, implementation string = result ∧
spec result

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  sorry

-- #test implementation "o o| .| o| o| .| .| .| .| o o" = [4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4]
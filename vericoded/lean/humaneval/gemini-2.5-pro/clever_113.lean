-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def count_odd_digits (s : String) : Nat :=
  (s.data.filter (fun c => c.isDigit ∧ c.toNat % 2 = 1)).length

-- LLM HELPER
def construct_output_string (n : Nat) : String :=
  "the number of odd elements " ++ n.repr ++ "n the str" ++ n.repr ++ "ng " ++ n.repr ++ " of the " ++ n.repr ++ "nput."
-- </vc-helpers>

-- <vc-definitions>
def implementation (lst: List String) : List String :=
  match lst with
  | [] => []
  | s :: ss =>
    let num_odd_digits := count_odd_digits s
    let new_s := construct_output_string num_odd_digits
    new_s :: implementation ss
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List String → List String)
-- inputs
(lst: List String) :=
-- spec
let spec (result : List String) :=
  lst.all (fun s => s.data.all (fun c => c.isDigit)) →
  (result.length = 0 ↔ lst.length = 0) ∧
  (result.length > 0 →
  let num_odd_digits := (lst.head!.data.filter (fun c => c.isDigit ∧ c.toNat % 2 = 1)).length
  result.head! = "the number of odd elements " ++ num_odd_digits.repr ++ "n the str" ++ num_odd_digits.repr ++ "ng " ++ num_odd_digits.repr ++ " of the " ++ num_odd_digits.repr ++ "nput."
  ∧ result.tail! = implementation lst.tail!)
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

theorem correctness
(lst: List String)
: problem_spec implementation lst
:= by
  use implementation lst
  constructor
  · rfl
  · dsimp [problem_spec]
    intro h_all_digits
    induction lst with
    | nil =>
      simp [implementation]
    | cons head tail ih =>
      simp [implementation, List.head!, List.tail!, count_odd_digits, construct_output_string]
-- </vc-theorems>

-- #test implementation ['1234567'] = ["the number of odd elements 4n the str4ng 4 of the 4nput."]
-- #test implementation ['3',"11111111"] = ["the number of odd elements 1n the str1ng 1 of the 1nput.",
--  "the number of odd elements 8n the str8ng 8 of the 8nput."]
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def count_odd_digits (s : String) : Nat :=
  s.data.filter (fun c => c.isDigit ∧ c.toNat % 2 = 1) |>.length

-- LLM HELPER
def format_output (count : Nat) : String :=
  "the number of odd elements " ++ count.repr ++ "n the str" ++ count.repr ++ "ng " ++ count.repr ++ " of the " ++ count.repr ++ "nput."

def implementation (lst: List String) : List String :=
  lst.map (fun s => format_output (count_odd_digits s))

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
  intro h_digits
  constructor
  · constructor
    · intro h_empty
      simp [implementation] at h_empty
      have : lst = [] := by
        rw [List.map_eq_nil] at h_empty
        exact h_empty
      rw [this]
      simp
    · intro h_empty
      simp [implementation]
      rw [h_empty]
      simp
  · intro h_nonempty
    constructor
    · simp [implementation, count_odd_digits, format_output]
      cases' lst with head tail
      · contradiction
      · simp
    · simp [implementation]
      cases' lst with head tail
      · contradiction
      · simp

-- #test implementation ['1234567'] = ["the number of odd elements 4n the str4ng 4 of the 4nput."]
-- #test implementation ['3',"11111111"] = ["the number of odd elements 1n the str1ng 1 of the 1nput.",
--  "the number of odd elements 8n the str8ng 8 of the 8nput."]
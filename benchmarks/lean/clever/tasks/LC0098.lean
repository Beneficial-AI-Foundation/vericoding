-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
import Std
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (s: String) : Option Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: String → Option Int)
-- inputs
(s: String) :=
-- spec
let numeric_characters := ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."]
let is_valid_string :=
  s.length > 0 ∧
  s.count (".".get! 0) ≤ 1 ∧
  s.count ("-".get! 0) ≤ 1 ∧
  s.data.all (fun c => numeric_characters.contains (String.mk [c])) ∧
  (s.count ("-".get! 0) = 1 → s.data.head! = '-')

let spec (result : Option Int) := match result with
  | some result =>
    is_valid_string ∧
    let parts := s.split (fun c => c = '.')
    (parts.length = 1 → result = s.toInt!) ∧
    (parts.length = 2 →
      let integer_part := parts[0]!
      let is_negative := s.data.head! = '-'
      |((integer_part.toInt! - result) : ℚ)| ≤ 0.5 ∧
      (is_negative → |((integer_part.toInt! - result) : ℚ)| = 0.5 → integer_part.toInt? < result) ∧
      (¬is_negative → |((integer_part.toInt! - result) : ℚ)| = 0.5 → integer_part.toInt? > result)
    )
  | none => ¬ is_valid_string
-- program termination
∃ result,
  implementation s = result ∧
  spec result

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  sorry
-- </vc-theorems>
-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: is_palindrome
use: |
  Helper to check if a string is a palindrome.
problems:
  - 10
  - 48
-/
def is_palindrome
(s: String): Bool :=
s = s.toList.reverse.asString
-- </vc-preamble>

-- <vc-helpers>
-- No helpers are needed for this problem.
-- </vc-helpers>

-- <vc-definitions>
def implementation (string: String) : Bool :=
  is_palindrome string
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(string: String) :=
-- spec
let spec (result: Bool) :=
result ↔ is_palindrome string
-- program termination
∃ result, implementation string = result ∧
spec result

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · unfold implementation
    rfl
-- </vc-theorems>

-- #test implementation "" = true
-- #test implementation "aba" = true
-- #test implementation "aaaaa" = true
-- #test implementation "zbcd" = false
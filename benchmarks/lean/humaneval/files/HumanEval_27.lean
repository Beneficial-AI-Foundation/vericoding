import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) : String :=
  sorry

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(string: String) :=
-- spec
let spec (result: String) :=
let chars_in_result := result.toList;
let chars_in_string := string.toList;
chars_in_result.length = string.length ∧
(∀ i, i < chars_in_result.length →
  let c := chars_in_result[i]!;
  let c' := chars_in_string[i]!;
  (c.isUpper → c'.isLower) ∧
  (c.isLower → c'.isUpper) ∧
  ((¬ c.isUpper ∧ ¬ c.isLower) → c = c')
);
-- program termination
∃ result, implementation string = result ∧
spec result

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  sorry

-- #test implementation "Hello" = "hELLO"
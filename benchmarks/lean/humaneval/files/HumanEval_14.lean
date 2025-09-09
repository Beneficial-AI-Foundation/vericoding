import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

def problem_spec
-- function signature
(implementation: String → List String)
-- inputs
(string: String) :=
-- spec
let spec (result: List String) :=
result.length = string.length ∧
∀ i, i < result.length →
result[i]! = string.take (i + 1);
-- program termination
∃ result, implementation string = result ∧
spec result

-- <vc-helpers>

-- </vc-helpers>

-- <vc-description>
/-
function_signature: "def all_prefixes(string: str) -> List[str]"
docstring: |
    Return list of all prefixes from shortest to longest of the input string
test_cases:
  - input: "abc"
    expected_output:
      - "a"
      - "ab"
      - "abc"
-/
-- </vc-description>

-- <vc-spec>
def implementation (string: String) : List String :=
-- </vc-spec>
-- <vc-code>
sorry
-- </vc-code>

-- <vc-theorem>
theorem correctness
(string: String)
: problem_spec implementation string
:=
-- </vc-theorem>
-- <vc-proof>
by
  sorry
-- </vc-proof>

-- #test implementation "abc" = ["a", "ab", "abc"]
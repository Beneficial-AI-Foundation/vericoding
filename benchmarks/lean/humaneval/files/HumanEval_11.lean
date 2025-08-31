/- 
function_signature: "def string_xor(a: str, b: str) -> str"
docstring: |
    Input are two strings a and b consisting only of 1s and 0s.
    Perform binary XOR on these inputs and return result also as a string.
test_cases:
  - input:
      - "010"
      - "110"
    expected_output: "100"
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (a b: String) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → String → String)
-- inputs
(a b: String) :=
-- spec
let spec (result: String) :=
  a.all (fun c => c = '0' ∨ c = '1') →
  b.all (fun c => c = '0' ∨ c = '1') →
  a.length = b.length →
  result.length = a.length ∧
  result.all (fun c => c = '0' ∨ c = '1') ∧
  (∀ i, i < a.length →
  let i_pos := String.Pos.mk i;
  (a.get i_pos = b.get i_pos → result.get i_pos = '0') ∧
  (a.get i_pos ≠ b.get i_pos → result.get i_pos = '1'));
-- program termination
∃ result, implementation a b = result ∧
spec result

theorem correctness
(a b: String)
: problem_spec implementation a b
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "010" "110" = "100"
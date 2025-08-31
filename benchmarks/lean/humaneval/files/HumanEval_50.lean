/- 
function_signature: "def encode_shift(s: String) -> String"
docstring: |
    returns encoded string by shifting every character by 5 in the alphabet.
test_cases:
  - input: abc
    expected_output: fgh
  - input: xyz
    expected_output: cde
  - input: aaa
    expected_output: fff
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (s: String) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s : String) :=
let isAlphabetic (string: String) : Bool :=
∀ i, i < string.length →
let c := string.get! ⟨i⟩;
('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)
-- spec
let spec (result: String) :=
isAlphabetic result ∧ isAlphabetic s ∧
result.length = s.length ∧
∃ k : Nat, k < 26 ∧
∀ i : Nat, i < s.length →
((s.get! ⟨i⟩).toNat + k) % 26 = (result.get! ⟨i⟩).toNat
→ k = 5
-- program termination
∃ result, implementation s = result ∧
spec result

theorem correctness
(s: String)
: problem_spec implementation s
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "abc" = "fgh"
-- #test implementation "xyz" = "cde"
-- #test implementation "aaa" = "fff"
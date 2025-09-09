import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) : Nat :=
  sorry

def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
let isVowel (c : Char) :=
  let vowels := "aeiouAEIOU"
  vowels.contains c
let isY (c : Char) := c = 'y' ∨ c = 'Y'
-- spec
let spec (result: Nat) :=
string.data.all (fun c => c.isAlpha) →
if string.length = 1 then
  result = if isVowel string.data[0]! ∨ isY string.data[0]! then 1 else 0
else
  result = (if isVowel string.data[0]! then 1 else 0) + implementation (string.drop 1);
-- program termination
∃ result, implementation string = result ∧
spec result

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  sorry

-- #test implementation "abcde" = 2
-- #test implementation "ACEDY" = 3
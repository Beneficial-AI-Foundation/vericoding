/- 
function_signature: "def hex_key(num: string) -> int"
docstring: |
    You have been tasked to write a function that receives
    a hexadecimal number as a string and counts the number of hexadecimal
    digits that are primes (prime number, or a prime, is a natural number
    greater than 1 that is not a product of two smaller natural numbers).
    Hexadecimal digits are 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F.
    Prime numbers are 2, 3, 5, 7, 11, 13, 17,...
    So you have to determine a number of the following digits: 2, 3, 5, 7,
    B (=decimal 11), D (=decimal 13).
    Note: you may assume the input is always correct or empty string,
    and symbols A,B,C,D,E,F are always uppercase.
test_cases:
  - input: "AB"
    expected_output: 1
  - input: "1077E"
    expected_output: 2
  - input: "ABED1A33"
    expected_output: 4
  - input: "123456789ABCDEF0"
    expected_output: 6
  - input: "2020"
    expected_output: 2
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (num: String) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → Int)
-- inputs
(num: String) :=
-- spec
let spec (result: Int) :=
  let num_val (ch : Char) :=
    if ch.isDigit then
      (ch.toNat - '0'.toNat)
    else if ch.isUpper then
      ((ch.toNat - 'A'.toNat) + 10)
    else 0;
  0 < num.length →
  (
    let char_val := num_val num.toList[0]!;
    (Nat.Prime char_val →
      (1 < num.length → result = char_val + implementation (num.drop 1)) ∧
      (1 = num.length → result = char_val)) ∧
    (¬Nat.Prime char_val →
      (1 < num.length → result = implementation (num.drop 1)) ∧
      (1 = num.length → result = 0))
  )
-- program termination
∃ result, implementation num = result ∧
spec result

theorem correctness
(num: String)
: problem_spec implementation num
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "AB" = 1
-- #test implementation "1077E" = 2
-- #test implementation "ABED1A33" = 4
-- #test implementation "2020" = 2
-- #test implementation "123456789ABCDEF0" = 6
-- #test implementation "112233445566778899AABBCCDDEEFF00" = 12
-- #test implementation "" = 0
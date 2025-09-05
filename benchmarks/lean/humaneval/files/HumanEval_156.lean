/- 
function_signature: "def int_to_mini_roman(num: Nat) -> String"
docstring: |
    Given a positive integer, obtain its roman numeral equivalent as a string,
    and return it in lowercase.
    Restrictions: 1 <= num <= 1000
test_cases:
  - input: 19
    expected_output: xix
  - input: 152
    expected_output: clii
  - input: 426
    expected_output: cdxxvi
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: romanCharToValue
use: |
  Map from valid characters and their values
problems:
  - 156
sample_problems: []
-/
def romanCharToValue : Char → Nat
| 'i' => 1
| 'v' => 5
| 'x' => 10
| 'l' => 50
| 'c' => 100
| 'd' => 500
| 'm' => 1000
| _   => 0

/--
name: validSubtractivePairs
use: |
  Legal subtractive pairs: first char can precede second for subtraction (in roman numerals)
problems:
  - 156
sample_problems: []
-/
def validSubtractivePairs : List (Char × Char) :=
  [('i', 'v'), ('i', 'x'), ('x', 'l'), ('x', 'c'), ('c', 'd'), ('c', 'm')]

/--
name: maxRepetitions
use: |
  Max allowed repetitions for each character (in roman numerals)
problems:
  - 156
sample_problems: []
-/
def maxRepetitions : Char → Nat
| 'i' | 'x' | 'c' | 'm' => 3
| 'v' | 'l' | 'd'       => 1
| _                    => 0

/--
name: countRepetitions
use: |
  Helper to count consecutive repetitions (in roman numerals)
problems:
  - 156
sample_problems: []
-/
def countRepetitions : List Char → Char → Nat → Nat
| [], _, n => n
| (h :: t), c, n => if h = c then countRepetitions t c (n + 1) else n

/--
name: validRepetition
use: |
  Helper to validate proper use of repetitions (in roman numerals)
problems:
  - 156
sample_problems: []
-/
partial def validRepetition : List Char → Bool
| [] => true
| c :: rest =>
  let max := maxRepetitions c
  let count := countRepetitions rest c 1
  count ≤ max ∧ validRepetition (rest.drop (count - 1))

/--
name: validSubtractiveOrder
use: |
  Helper to validate legal subtractive combinations (in roman numerals)
problems:
  - 156
sample_problems: []
-/
def validSubtractiveOrder : List Char → Bool
| [] | [_] => true
| c1 :: c2 :: rest =>
  match romanCharToValue c1, romanCharToValue c2 with
  | v1, v2 =>
    if v1 < v2 then
      -- check if c1 and c2 form a legal subtractive pair
      (c1, c2) ∈ validSubtractivePairs ∧ validSubtractiveOrder rest
    else if v1 = 0 ∨ v2 = 0 then
      false
    else
      validSubtractiveOrder (c2 :: rest)

/--
name: isValidRoman
use: |
  Function to check if a string is a roman numeral
problems:
  - 156
sample_problems: []
-/
def isValidRoman (s : String) : Bool :=
  s.data.all (λ c => romanCharToValue c ≠ 0) ∧
  validRepetition s.data ∧
  validSubtractiveOrder s.data

/--
name: romanToDecimalAux
use: |
  Helper to convert list of roman characters to decimal
problems:
  - 156
sample_problems: []
-/
def romanToDecimalAux : List Char → Nat
| [] => 0
| c1 :: c2 :: rest =>
    let val1 := romanCharToValue c1
    let val2 := romanCharToValue c2
    if val1 < val2 then
      -- subtractive notation
      (val2 - val1) + romanToDecimalAux rest
    else
      val1 + romanToDecimalAux (c2 :: rest)
| [c] => romanCharToValue c

/--
name: romanToDecimal
use: |
  Function to convert a valid lowercase Roman numeral string to Nat
problems:
  - 156
sample_problems: []
-/
def romanToDecimal (s : String) : Nat :=
  romanToDecimalAux s.data

-- <vc-helpers>
-- </vc-helpers>

def implementation (num: Nat) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: Nat → String)
-- inputs
(num: Nat) :=
-- spec
let spec (result: String) :=
1 ≤ num ∧ num ≤ 1000 ∧ (result.data.all (fun c => c.isLower)) →
isValidRoman result ∧ romanToDecimal result = num
-- program terminates
∃ result, impl num = result ∧
-- return value satisfies spec
spec result

theorem correctness
(num: Nat)
: problem_spec implementation num :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 19 = "xix"
-- #test implementation 152 = "clii"
-- #test implementation 426 = "cdxxvi"
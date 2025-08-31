/- 
function_signature: "def do_algebra(operator: List String, operand: List Nat) -> Int"
docstring: |
    Given two lists operator, and operand. The first list has basic algebra operations, and
    the second list is a list of integers. Use the two given lists to build the algebric
    expression and return the evaluation of this expression.

    The basic algebra operations:
    Addition ( + )
    Subtraction ( - )
    Multiplication ( * )
    Floor division ( // )
    Exponentiation ( ** )

    Note:
        The length of operator list is equal to the length of operand list minus one.
        Operand is a list of of non-negative integers.
        Operator list has at least one operator, and operand list has at least two operands.
test_cases:
  - input: [['+', '*', '-'], [2, 3, 4, 5]]
    expected_output: 9
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (operator: List String) (operand : List Nat) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: List String → List Nat → Int)
-- inputs
(operator : List String)
(operand : List Nat) :=
-- spec
let spec (result: Int) :=
operator.length = operand.length - 1 ∧ 0 < operator.length ∧ operand.all (fun n => 0 ≤ n) →
let inline_tokens : List String := mergeAlternately operand operator
evalArith_precedence inline_tokens result
-- program terminates
∃ result, impl operator operand = result ∧
-- return value satisfies spec
spec result

theorem correctness
(operator : List String) (operand : List Nat)
: problem_spec implementation operator operand :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation ['+', '*', '-'] [2,3,4,5] = 9
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

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: mergeAlternately
use: |
  Helper Methods to mergeAlternately a list of strings
problems:
  - 160
sample_problems: []
-/
def mergeAlternately : List Nat → List String → List String
| [], []       => []
| [], y :: ys  => y :: mergeAlternately [] ys
| x :: xs, []  => x.repr :: mergeAlternately xs []
| x :: xs, y :: ys => x.repr :: y :: mergeAlternately xs ys

/--
name: applyOp
use: |
  Helper method to apply operations on two integers
problems:
  - 160
sample_problems: []
-/
def applyOp (x y : Int) : String → Option Int
  | "+"  => some (x + y)
  | "-"  => some (x - y)
  | "*"  => some (x * y)
  | "//" => if y == 0 then none else some (x / y)
  | "**" =>
    if x < 0 then none
    else some (Int.ofNat ((Int.toNat x) ^ (Int.toNat y)))
  | _     => none

/--
name: evalArith_pass
use: |
  Noncomputable relational spec for a single step evaluation (any op, ignoring precedence).
problems:
  - 160
sample_problems: []
-/
inductive evalArith_pass : List String → Int → Prop
| num {s : String} {n : Nat} (h : s.toNat! = n) :
    evalArith_pass [s] (Int.ofNat n)
| binOp {ts1 ts2 : List String} {op : String} {r1 r2 r : Int}
    (h1 : evalArith_pass ts1 r1)
    (h2 : evalArith_pass ts2 r2)
    (hop : applyOp r1 r2 op = some r) :
    evalArith_pass (ts1 ++ op :: ts2) r

/--
name: evalArith_exp
use: |
  Relational spec for exponentiation (highest precedence).
problems:
  - 160
sample_problems: []
-/
inductive evalArith_exp : List String → Int → Prop
| of_pass {ts r} (h : evalArith_pass ts r) : evalArith_exp ts r
| step {ts1 ts2 r1 r2 r} (h1 : evalArith_exp ts1 r1) (h2 : evalArith_exp ts2 r2)
    (hop : applyOp r1 r2 "**" = some r) :
    evalArith_exp (ts1 ++ "**" :: ts2) r

/--
name: evalArith_mul
use: |
  Relational spec for multiplication/division (middle precedence).
problems:
  - 160
sample_problems: []
-/
inductive evalArith_mul : List String → Int → Prop
| of_exp {ts r} (h : evalArith_exp ts r) : evalArith_mul ts r
| step {ts1 ts2 r1 r2 r} (h1 : evalArith_mul ts1 r1) (h2 : evalArith_mul ts2 r2)
    (hop : applyOp r1 r2 "*" = some r ∨ applyOp r1 r2 "//" = some r) :
    evalArith_mul (ts1 ++ "*" :: ts2) r

/--
name: evalArith_add
use: |
  Relational spec for addition/subtraction (lowest precedence).
problems:
  - 160
sample_problems: []
-/
inductive evalArith_add : List String → Int → Prop
| of_mul {ts r} (h : evalArith_mul ts r) : evalArith_add ts r
| step {ts1 ts2 r1 r2 r} (h1 : evalArith_add ts1 r1) (h2 : evalArith_add ts2 r2)
    (hop : applyOp r1 r2 "+" = some r ∨ applyOp r1 r2 "-" = some r) :
    evalArith_add (ts1 ++ "+" :: ts2) r

/--
name: evalArith_precedence
use: |
  Main function to evaluate an expression
problems:
  - 160
sample_problems: []
-/
def evalArith_precedence (ts : List String) (r : Int) : Prop :=
  evalArith_add ts r

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
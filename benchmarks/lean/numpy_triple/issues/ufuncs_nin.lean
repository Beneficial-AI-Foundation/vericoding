-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "nin",
  "description": "The number of input arguments",
  "examples": {
    "add.nin": "2",
    "sin.nin": "1",
    "modf.nin": "1"
  }
}
-/

/-- Enumeration of common NumPy universal functions (ufuncs).
    This represents the different types of ufuncs that have nin properties. -/
inductive UfuncType where
  /-- Binary arithmetic operation: element-wise addition (a + b) -/
  | add
  /-- Binary arithmetic operation: element-wise subtraction (a - b) -/
  | subtract
  /-- Binary arithmetic operation: element-wise multiplication (a * b) -/
  | multiply
  /-- Binary arithmetic operation: element-wise division (a / b) -/
  | divide
  /-- Binary arithmetic operation: element-wise exponentiation (a ** b) -/
  | power
  /-- Unary trigonometric function: sine of elements -/
  | sin
  /-- Unary trigonometric function: cosine of elements -/
  | cos
  /-- Unary exponential function: e raised to the power of elements -/
  | exp
  /-- Unary logarithmic function: natural logarithm of elements -/
  | log
  /-- Unary square root function: square root of elements -/
  | sqrt
  /-- Unary absolute value function: absolute value of elements -/
  | abs
  /-- Unary function returning fractional and integer parts of elements -/
  | modf
  deriving DecidableEq

/-- Returns the number of input arguments for a given ufunc type.
    Binary operations return 2, unary operations return 1. -/
def nin (ufunc : UfuncType) : Id Nat :=
  match ufunc with
  | .add => pure 2
  | .subtract => pure 2
  | .multiply => pure 2
  | .divide => pure 2
  | .power => pure 2
  | .sin => pure 1
  | .cos => pure 1
  | .exp => pure 1
  | .log => pure 1
  | .sqrt => pure 1
  | .abs => pure 1
  | .modf => pure 1

/-- Helper definition: the set of binary ufuncs (those requiring 2 inputs) -/
def binaryUfuncs : List UfuncType := [.add, .subtract, .multiply, .divide, .power]

/-- Helper definition: the set of unary ufuncs (those requiring 1 input) -/
def unaryUfuncs : List UfuncType := [.sin, .cos, .exp, .log, .sqrt, .abs, .modf]

/-- Specification: nin returns the correct number of input arguments for each ufunc type.
    
    For binary ufuncs (add, subtract, multiply, divide, power), nin returns 2.
    For unary ufuncs (sin, cos, exp, log, sqrt, abs, modf), nin returns 1.
    
    This property is essential for ufunc introspection and validates that the
    number of inputs matches the mathematical definition of each operation.
    
    Key properties:
    1. Binary operations consistently return 2 inputs
    2. Unary operations consistently return 1 input  
    3. All ufuncs are classified as either binary or unary
    4. The result is always a positive integer (1 or 2) -/
theorem nin_spec (ufunc : UfuncType) :
    ⦃⌜True⌝⦄
    nin ufunc
    ⦃⇓result => ⌜(ufunc ∈ binaryUfuncs → result = 2) ∧
                  (ufunc ∈ unaryUfuncs → result = 1) ∧
                  (ufunc ∈ binaryUfuncs ∨ ufunc ∈ unaryUfuncs) ∧
                  (result > 0) ∧
                  (result ≤ 2)⌝⦄ := by
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>
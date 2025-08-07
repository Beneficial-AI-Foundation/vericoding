import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic

/-- Merge two strings alternately -/
def mergeAlternately (s1 s2 : String) : String := sorry

/-- Evaluate arithmetic expression with precedence -/
def evalArith_precedence (expr : String) : Int := sorry

def problem_spec
(implementation: List String → List Nat → Int)
(operator : List String)
(operand : List Nat) :=
let spec (result: Int) :=
operator.length = operand.length - 1 ∧ 0 < operator.length ∧ operand.all (fun n => 0 ≤ n) →
let inline_tokens : String := sorry -- mergeAlternately of operand and operator
result = evalArith_precedence inline_tokens
∃ result, implementation operator operand = result ∧
spec result

def implementation (operator: List String) (operand : List Nat) : Int := sorry

theorem correctness
(operator : List String) (operand : List Nat)
: problem_spec implementation operator operand := sorry 
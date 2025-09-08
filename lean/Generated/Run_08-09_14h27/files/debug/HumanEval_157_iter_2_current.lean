import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a b c: Nat) : Bool :=
  0 < a && 0 < b && 0 < c && 
  (a * a + b * b = c * c || a * a + c * c = b * b || b * b + c * c = a * a)

def problem_spec
-- function signature
(impl: Nat → Nat → Nat → Bool)
-- inputs
(a b c: Nat) :=
-- spec
let spec (result: Bool) :=
result ↔
  0 < a ∧ 0 < b ∧ 0 < c ∧
  ((a * a + b * b = c * c) ∨
  (a * a + c * c = b * b) ∨
  (b * b + c * c = a * a))
-- program terminates
∃ result, impl a b c = result ∧
-- return value satisfies spec
spec result

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  unfold problem_spec implementation
  use (0 < a && 0 < b && 0 < c && 
       (a * a + b * b = c * c || a * a + c * c = b * b || b * b + c * c = a * a))
  constructor
  · rfl
  · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true]
    constructor
    · intro h
      exact h
    · intro h
      exact h

-- #test implementation ([1, 2, 2, -4]: List Int) = (-9: Int)
-- #test implementation ([0, 1]: List Int) = (0: Int)
-- #test implementation ([]: List Int) = none
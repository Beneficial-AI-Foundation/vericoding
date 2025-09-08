import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a b c: Nat) : List Nat :=
  let eaten := min b c
  [a + eaten, c - eaten]

def problem_spec
-- function signature
(impl: Nat → Nat → Nat → List Nat)
-- inputs
(number need remaining: Nat) :=
-- spec
let spec (result: List Nat) :=
number ≤ 1000 → need ≤ 1000 → remaining ≤ 1000 →
result.length = 2 ∧
(need ≤ remaining → result[0]! - need = number ∧
need = remaining - result[1]!) ∧
(remaining < need → result[0]! - remaining = number ∧
result[1]! = 0);
-- program terminates
∃ result, impl number need remaining = result ∧
-- return value satisfies spec
spec result

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  simp [problem_spec, implementation]
  use [a + min b c, c - min b c]
  simp [List.length_cons, List.length_nil]
  constructor
  · rfl
  · intro h1 h2 h3
    constructor
    · simp
      constructor
      · intro h4
        simp [List.get!_cons_zero, List.get!_cons_succ]
        constructor
        · simp [min_eq_left h4]
        · simp [min_eq_left h4]
      · intro h4
        simp [List.get!_cons_zero, List.get!_cons_succ]
        constructor
        · simp [min_eq_right (le_of_not_ge h4)]
        · simp [min_eq_right (le_of_not_ge h4)]
          rw [Nat.sub_self]
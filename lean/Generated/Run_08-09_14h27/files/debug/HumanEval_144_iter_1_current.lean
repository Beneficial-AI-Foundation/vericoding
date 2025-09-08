/- 
function_signature: "def simplify(x: str, n: str) -> Bool"
docstring: |
    Your task is to implement a function that will simplify the expression
    x * n. The function returns True if x * n evaluates to a whole number and False
    otherwise. Both x and n, are string representation of a fraction, and have the following format,
    <numerator>/<denominator> where both numerator and denominator are positive whole numbers.

    You can assume that x, and n are valid fractions, and do not have zero as denominator.
test_cases:
  - input: ["1/5", "5/1"]
    expected_output: True
  - input: ["1/6", "2/1"]
    expected_output: False
  - input: ["7/10", "10/2"]
    expected_output: False
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (x: String) (n: String) : Bool :=
  let fx := x.splitOn "/"
  let fn := n.splitOn "/"
  if fx.length = 2 && fn.length = 2 && fx.all String.isNat && fn.all String.isNat then
    let p1 := fx[0]!.toNat!
    let q1 := fx[1]!.toNat!
    let p2 := fn[0]!.toNat!
    let q2 := fn[1]!.toNat!
    if q1 ≠ 0 && q2 ≠ 0 then
      (q1 * q2) % (p1 * p2) = 0
    else
      false
  else
    false

def problem_spec
-- function signature
(impl: String → String → Bool)
-- inputs
(x: String) (n: String) :=
-- spec
let spec (result: Bool) :=
let fx := x.splitOn "/";
let fn := n.splitOn "/";
fx.length = 2 → fn.length = 2 →
fx.all String.isNat → fn.all String.isNat →
let p1 := fx[0]!.toNat!;
let q1 := fx[1]!.toNat!;
let p2 := fn[0]!.toNat!;
let q2 := fn[1]!.toNat!;
q1 ≠ 0 → q2 ≠ 0 →
(result ↔ (∃ k, k * p1 * p2 = q1 * q2))
-- program termination
∃ result, impl x n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma mod_eq_zero_iff_divisible (a b : Nat) : a % b = 0 ↔ ∃ k, k * b = a := by
  simp [Nat.dvd_iff_mod_eq_zero]

theorem correctness
(x: String) (n: String)
: problem_spec implementation x n := by
  unfold problem_spec
  simp [implementation]
  let fx := x.splitOn "/"
  let fn := n.splitOn "/"
  by_cases h1 : fx.length = 2 ∧ fn.length = 2 ∧ fx.all String.isNat ∧ fn.all String.isNat
  · simp [h1]
    let p1 := fx[0]!.toNat!
    let q1 := fx[1]!.toNat!
    let p2 := fn[0]!.toNat!
    let q2 := fn[1]!.toNat!
    by_cases h2 : q1 ≠ 0 ∧ q2 ≠ 0
    · simp [h2]
      constructor
      · intro h3 h4 h5 h6 h7 h8
        rw [mod_eq_zero_iff_divisible]
        constructor
        · intro ⟨k, hk⟩
          use k
          rw [← hk]
          ring
        · intro ⟨k, hk⟩
          use k
          rw [hk]
          ring
      · exact h1.1
    · simp [h2]
      intro h3 h4 h5 h6
      exfalso
      exact h2 ⟨h5, h6⟩
  · simp [h1]
    intro h2
    exfalso
    exact h1 ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩

-- #test implementation "1/5" "5/1" = True
-- #test implementation "1/6" "2/1" = False
-- #test implementation "7/10" "10/2" = False
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (x: String) (n: String) : Bool :=
  sorry

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

theorem correctness
(x: String) (n: String)
: problem_spec implementation x n := by
  sorry

-- #test implementation "1/5" "5/1" = True
-- #test implementation "1/6" "2/1" = False
-- #test implementation "7/10" "10/2" = False
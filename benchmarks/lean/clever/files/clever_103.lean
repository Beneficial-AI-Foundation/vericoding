-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (n: Nat) (m: Nat) : Option String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: Nat → Nat → Option String)
-- inputs
(n: Nat) (m: Nat) :=
-- spec
let spec (result: Option String) :=
  (n > m ↔ result.isNone) ∧
  (n ≤ m ↔ result.isSome) ∧
  (n ≤ m →
    (result.isSome ∧
    let val := Option.getD result "";
    let xs := List.Ico n (m+1);
    let avg := xs.sum / xs.length;
    (val.take 2 = "0b") ∧
    (Nat.ofDigits 2 ((val.drop 2).toList.map (fun c => c.toNat - '0'.toNat)).reverse = avg)))
-- program termination
∃ result, implementation n m = result ∧
spec result

theorem correctness
(n: Nat) (m: Nat)
: problem_spec implementation n m
:= by
  sorry
-- </vc-theorems>
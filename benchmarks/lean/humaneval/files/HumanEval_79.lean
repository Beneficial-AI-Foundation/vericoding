import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (decimal: Nat) : String :=
  sorry

def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(decimal: Nat) :=
-- spec
let spec (result: String) :=
  4 < result.length ∧
  result.drop (result.length - 2) = "db" ∧
  result.take 2 = "db" ∧
  let resultTrimmed := (result.toList.drop 2).dropLast.dropLast.map (fun c => c.toNat - '0'.toNat)
  decimal = Nat.ofDigits 2 resultTrimmed.reverse
-- program termination
∃ result, implementation decimal = result ∧
spec result

theorem correctness
(decimal: Nat)
: problem_spec implementation decimal
:= by
  sorry

-- #test implementation 0 = "db0db"
-- #test implementation 32 = "db100000db"
-- #test implementation 103 = "db1100111db"
-- #test implementation 15 = "db1111db"
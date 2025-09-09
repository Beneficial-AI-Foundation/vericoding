import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a b: String) : Bool :=
  sorry

def problem_spec
-- function signature
(impl: String → String → Bool)
-- inputs
(a b: String) :=
-- spec
let spec (result: Bool) :=
(b.length = 0 → result) ∧
(0 < b.length →
result ↔ ((b.length ≤ a.length) ∧
  (∃ i : Nat, i < b.length ∧
  let b_rotation := b.drop i ++ b.take i;
  a.containsSubstr b_rotation)));
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

theorem correctness
(a b: String)
: problem_spec implementation a b := by
  sorry

-- #test implementation "abcd" "abd" = False
-- #test implementation "hello" "ell" = True
-- #test implementation "whassup" "psus" = False
-- #test implementation "abab" "baa" = True
-- #test implementation "efef" "eeff" = False
-- #test implementation "himenss" "simen" = True
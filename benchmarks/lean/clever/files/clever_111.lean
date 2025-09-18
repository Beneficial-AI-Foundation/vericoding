-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (s: String) : Std.HashMap Char Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: String → Std.HashMap Char Nat)
-- inputs
(s: String) :=
-- spec
let spec (result : Std.HashMap Char Nat) :=
    let chars := s.splitOn " "
    chars.all (fun c => c.length = 1) ∧ s.all (fun c => c.isLower ∨ c = ' ') →
    ∀ key ∈ result.keys,
      (key.isLower ∧
      key ∈ s.data ∧
      result.get! key = s.count key) ∧
    (∀ char ∈ s.data, char.isLower →
      ((∃ char2 ∈ s.data, char2.isLower ∧ char2 ≠ char ∧
      s.count char < s.count char2) ↔ char ∉ result.keys))
-- program termination
∃ result,
  implementation s = result ∧
  spec result

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  sorry
-- </vc-theorems>

-- #test implementation 'a b c' = {'a': 1, 'b': 1, 'c': 1}
-- #test implementation 'a b b a' = {'a': 2, 'b': 2}
-- #test implementation 'a b c a b' = {'a': 2, 'b': 2}
-- #test implementation 'b b b b a' = {'b': 4}
-- #test implementation '' = {}
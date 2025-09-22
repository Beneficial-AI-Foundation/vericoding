-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (s: String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(s: String) :=
-- spec
let spec (result : Nat) :=
  let is_sentence_is_boredom (s: String) : Bool :=
    (s.startsWith "I " ∨ s.startsWith " I") ∧ '.' ∉ s.data ∧ '?' ∉ s.data ∧ '!' ∉ s.data
  match s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
  | some i =>
    let j := i + 1;
    let substring := s.drop j;
    result = (if is_sentence_is_boredom substring then 1 else 0) + implementation substring
  | none =>
    result = if is_sentence_is_boredom s then 1 else 0
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
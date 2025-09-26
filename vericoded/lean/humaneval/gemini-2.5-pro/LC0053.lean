-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- No helper definitions are required for this problem.
-- The implementation uses `Finset` from Mathlib to represent the set of characters
-- in a string, and the proof relies on standard lemmas about `Finset` and `List`.
-- </vc-helpers>

-- <vc-definitions>
def implementation (s0 s1: String) : Bool :=
  s0.toList.toFinset == s1.toList.toFinset
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(impl: String → String → Bool)
-- inputs
(s0 s1: String) :=
-- spec
let spec (res: Bool) :=
  res ↔ (∀ c : Char, c ∈ s0.toList ↔ c ∈ s1.toList)
-- program terminates
∃ result, impl s0 s1 = result ∧
-- return value satisfies spec
spec result
-- if result then spec else ¬spec

theorem correctness
(s0 s1: String)
: problem_spec implementation s0 s1  := by
  unfold problem_spec
  use implementation s0 s1
  dsimp -- unfold the `let` binding of `spec`
  -- The goal becomes: implementation s0 s1 ↔ (∀ c, c ∈ s0.toList ↔ c ∈ s1.toList)
  -- Now we can prove this equivalence by simplifying both sides.
  simp [implementation, beq_iff_eq, Finset.ext_iff, List.mem_toFinset]
-- </vc-theorems>

-- #test implementation 'eabcdzzzz' 'dddzzzzzzzddeddabc' = true
-- #test implementation 'abcd' 'dddddddabc' = true
-- #test implementation 'dddddddabc' 'abcd' = true
-- #test implementation 'eabcd' 'dddddddabc' = false
-- #test implementation 'abcd' 'dddddddabce' = false
-- #test implementation 'eabcdzzzz' 'dddzzzzzzzddddabc' = false
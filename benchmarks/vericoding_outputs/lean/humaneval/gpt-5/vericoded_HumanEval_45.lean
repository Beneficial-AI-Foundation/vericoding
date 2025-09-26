-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def implementation (a h: Rat) : Rat :=
  if a = 0 then 0 else (a * h) / 2
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: Rat → Rat -> Rat)
-- inputs
(a h: Rat) :=
-- spec
let spec (result: Rat) :=
  a = 0 → result = 0 ∧
  (a ≠ 0 → (2 * result) / a = h);
-- -- program termination
∃ result, implementation a h = result ∧
spec result

theorem correctness
(a h : Rat)
: problem_spec implementation a h
:= by
  unfold problem_spec
  refine (by
    let spec (result : Rat) := a = 0 → result = 0 ∧ (a ≠ 0 → (2 * result) / a = h)
    refine ⟨implementation a h, rfl, ?_⟩
    intro ha0
    constructor
    · simp [implementation, ha0]
    · intro hne
      exact (hne (by simpa using ha0)).elim
  )
-- </vc-theorems>

-- #test implementation 5 3 = 7.5
-- #test implementation 8 2 = 8.0
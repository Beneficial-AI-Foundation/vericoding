import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Helper: reciprocal of 4*a - makes expressions more readable. -/
def one_over_four (a : Float) : Float := 1 / (4 * a)

/-- LLM HELPER
Trivial lemma: one_over_four equals the corresponding fraction. -/
theorem one_over_four_eq (a : Float) : one_over_four a = 1 / (4 * a) := rfl

-- </vc-helpers>

-- <vc-definitions>
def ParabolaDirectrix (a : Float) (h : Float) (k : Float) : Float :=
k - 1/(4*a)
-- </vc-definitions>

-- <vc-theorems>
theorem ParabolaDirectrix_spec (a h k : Float) :
a ≠ 0 →
ParabolaDirectrix a h k = k - 1/(4*a) :=
fun _ => rfl
-- </vc-theorems>

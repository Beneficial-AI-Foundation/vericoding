import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
set_option linter.unusedVariables false
-- </vc-helpers>

-- <vc-definitions>
def ParabolaDirectrix (a : Float) (h : Float) (k : Float) : Float :=
  k - (1 : Float) / (4 * a)
-- </vc-definitions>

-- <vc-theorems>
theorem ParabolaDirectrix_spec (a h k : Float) :
a ≠ 0 →
ParabolaDirectrix a h k = k - 1/(4*a) :=
by intro hn; rfl
-- </vc-theorems>

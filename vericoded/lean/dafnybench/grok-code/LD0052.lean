import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def CalDiv : Int × Int :=
(191 / 7, 191 % 7)
-- </vc-definitions>

-- <vc-theorems>
theorem CalDiv_spec :
let (x, y) := CalDiv
x = 191 / 7 ∧ y = 191 % 7 :=
by
  simp [CalDiv]
-- </vc-theorems>

import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Helper: explicit type ascriptions for numerals used below. -/
def i191 : Int := 191
def i7 : Int := 7

-- </vc-helpers>

-- <vc-definitions>
def CalDiv : Int × Int :=
(i191 / i7, i191 % i7)
-- </vc-definitions>

-- <vc-theorems>
theorem CalDiv_spec :
let (x, y) := CalDiv
x = 191 / 7 ∧ y = 191 % 7 :=
by
  dsimp [CalDiv, i191, i7]
  constructor
  rfl
  rfl

-- </vc-theorems>

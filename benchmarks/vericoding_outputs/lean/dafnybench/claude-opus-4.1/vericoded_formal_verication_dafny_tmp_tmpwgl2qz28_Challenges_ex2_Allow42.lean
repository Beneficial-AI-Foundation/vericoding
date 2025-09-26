import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helper needed, regular division works fine
-- </vc-helpers>

-- <vc-definitions>
def Allow42 (x : Int) (y : Int) : Int × Bool :=
if y = 42 then
    (0, true)
  else
    (x / (42 - y), false)
-- </vc-definitions>

-- <vc-theorems>
theorem Allow42_spec (x y : Int) :
let (z, err) := Allow42 x y
(y ≠ 42 → z = x/(42-y) ∧ err = false) ∧
(y = 42 → z = 0 ∧ err = true) :=
by
  simp only [Allow42]
  split
  · next heq =>
    simp [heq]
  · next hne =>
    constructor
    · intro _
      simp
    · intro heq
      exfalso
      exact hne heq
-- </vc-theorems>

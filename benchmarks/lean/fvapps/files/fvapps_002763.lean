-- <vc-preamble>
def volume (radius height : Float) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pi : Float := 3.14159
-- </vc-definitions>

-- <vc-theorems>
theorem volume_zero :
  volume 0 0 = 0 :=
  sorry

/- π is approximated as 3.14159 -/

/-
info: 153
-/
-- #guard_msgs in
-- #eval volume 7 3

/-
info: 98520
-/
-- #guard_msgs in
-- #eval volume 56 30

/-
info: 0
-/
-- #guard_msgs in
-- #eval volume 0 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
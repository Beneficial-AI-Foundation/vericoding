-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findSum (n : Int) : Int := sorry

theorem findSum_six :
  findSum 6 = 14 := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 8
-/
-- #guard_msgs in
-- #eval findSum 5

/-
info: 33
-/
-- #guard_msgs in
-- #eval findSum 10

/-
info: 2418
-/
-- #guard_msgs in
-- #eval findSum 100
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
-- <vc-preamble>
def Real := Int -- Simplified for demo

def does_fred_need_houseboat (x y : Int) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pi : Int := 3 -- Simplified for demo

def ceil (r : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem does_fred_need_houseboat_nonnegative {x y : Int} (h : y ≥ 0) :
  does_fred_need_houseboat x y ≥ 0 := by
  sorry

theorem does_fred_need_houseboat_symmetric {x y : Int} (h : y ≥ 0) :
  does_fred_need_houseboat x y = does_fred_need_houseboat (-x) y := by
  sorry

theorem does_fred_need_houseboat_increases {x y cx cy : Int}
  (h1 : y ≥ 0)
  (h2 : x.natAbs > 0 ∨ y > 0)
  (h3 : cx = x / 2)
  (h4 : cy = y / 2) :
  does_fred_need_houseboat x y ≥ does_fred_need_houseboat cx cy := by
  sorry

theorem does_fred_need_houseboat_formula {x y : Int} (h : y ≥ 0) :
  does_fred_need_houseboat x y = ceil (pi * ((x * x) + (y * y)) / 100) := by
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval does_fred_need_houseboat 1 1

/-
info: 20
-/
-- #guard_msgs in
-- #eval does_fred_need_houseboat 25 0

/-
info: 7
-/
-- #guard_msgs in
-- #eval does_fred_need_houseboat 10 10
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded
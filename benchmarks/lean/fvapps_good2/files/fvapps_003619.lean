-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Real := Int

def does_fred_need_houseboat (x y : Int) : Int :=
  sorry

def pi : Int := 3

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
-- </vc-theorems>
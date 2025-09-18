-- <vc-preamble>
def abs (x : Int) : Int := 
  if x ≥ 0 then x else -x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_john_lying (x y steps : Int) : Bool := sorry

theorem symmetry_properties {x y steps : Int} (h : steps ≥ 0) :
  is_john_lying x y steps = is_john_lying (-x) y steps ∧
  is_john_lying x y steps = is_john_lying x (-y) steps ∧
  is_john_lying x y steps = is_john_lying y x steps := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_steps_required {x y : Int} :
  ¬(is_john_lying x y (abs x + abs y - 1)) := sorry

theorem parity_constraint {x y extra_steps : Int} (h : extra_steps ≥ 0) :
  let min_steps := abs x + abs y
  let steps := min_steps + extra_steps
  if extra_steps % 2 = 0 then 
    is_john_lying x y steps = (steps ≥ min_steps)
  else
    ¬(is_john_lying x y steps) := sorry
-- </vc-theorems>
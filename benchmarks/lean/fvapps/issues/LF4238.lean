-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bear_fur : List Color → Color
  | _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bear_fur_valid_output (bears : List Color)
  (h : bears.length = 2) :
  bear_fur bears ∈ [Color.black, Color.white, Color.brown] ∨
  bear_fur bears = Color.brown ∨  -- representing "dark brown"
  bear_fur bears = Color.brown ∨  -- representing "light brown" 
  bear_fur bears = Color.black    -- representing "grey"
  := by sorry

theorem bear_fur_same_color (c : Color) :
  bear_fur [c, c] = c := by sorry

theorem bear_fur_order_invariant (c1 c2 : Color) :
  bear_fur [c1, c2] = bear_fur [c2, c1] := by sorry

theorem bear_fur_specific_pairs :
  (bear_fur [Color.black, Color.brown] = Color.brown) ∧   -- dark brown
  (bear_fur [Color.brown, Color.white] = Color.brown) ∧   -- light brown
  (bear_fur [Color.black, Color.white] = Color.black)     -- grey
  := by sorry

/-
info: 'black'
-/
-- #guard_msgs in
-- #eval bear_fur ["black", "black"]

/-
info: 'white'
-/
-- #guard_msgs in
-- #eval bear_fur ["white", "white"]

/-
info: 'brown'
-/
-- #guard_msgs in
-- #eval bear_fur ["brown", "brown"]

/-
info: 'dark brown'
-/
-- #guard_msgs in
-- #eval bear_fur ["black", "brown"]

/-
info: 'grey'
-/
-- #guard_msgs in
-- #eval bear_fur ["black", "white"]

/-
info: 'light brown'
-/
-- #guard_msgs in
-- #eval bear_fur ["brown", "white"]

/-
info: 'unknown'
-/
-- #guard_msgs in
-- #eval bear_fur ["pink", "black"]
-- </vc-theorems>
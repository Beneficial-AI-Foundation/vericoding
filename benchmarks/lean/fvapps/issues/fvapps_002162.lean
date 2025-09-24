-- <vc-preamble>
def isOnPerimeter (p : Point) (R C : Int) : Bool :=
  sorry

def validPairs (p1 p2 : Point) (R C : Int) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def canDrawCurves (R C N : Int) (pairs : List (Point × Point)) : String :=
  sorry

-- Theorem: Output is either YES or NO
-- </vc-definitions>

-- <vc-theorems>
theorem output_format (R C N : Int) (pairs : List (Point × Point)) :
  (canDrawCurves R C N pairs = "YES") ∨ (canDrawCurves R C N pairs = "NO") :=
  sorry

-- Theorem: Empty list of pairs always returns YES

theorem empty_pairs_is_yes (R C : Int) :
  canDrawCurves R C 0 [] = "YES" :=
  sorry

-- Theorem: Same point pairs always return YES

theorem same_point_pairs (R C : Int) (p : Point) :
  isOnPerimeter p R C → canDrawCurves R C 1 [(p, p)] = "YES" :=
  sorry

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval can_draw_curves 4 2 3 [[0, 1, 3, 1], [1, 1, 4, 1], [2, 0, 2, 2]]

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval can_draw_curves 2 2 4 [[0, 0, 2, 2], [2, 0, 0, 1], [0, 2, 1, 2], [1, 1, 2, 1]]

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval can_draw_curves 1 1 2 [[0, 0, 1, 1], [1, 0, 0, 1]]
-- </vc-theorems>
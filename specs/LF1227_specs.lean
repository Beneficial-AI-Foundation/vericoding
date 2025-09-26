-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def build_two_towers (n : Nat) (k : Nat) (heights : List Nat) : Int := sorry

/- Single box twice the height of k always returns -1 -/
-- </vc-definitions>

-- <vc-theorems>
theorem single_tall_box_impossible (height : Nat) :
  build_two_towers 1 height [2 * height] = -1 := sorry

/- Given a list of heights, building towers of minimum height is always possible -/

theorem min_height_possible (heights : List Nat) (h : heights.length ≥ 2) :
  let n := heights.length
  let k := heights.minimum?
  match k with
  | none => True 
  | some k => build_two_towers n k heights ≠ -1
  := sorry

/- List elements in different order produce the same result -/

theorem permutation_preserves_result (heights1 heights2 : List Nat) 
    (h1 : heights1.length ≥ 2)
    (h2 : heights1.isPerm heights2) :
  let n := heights1.length
  let k := heights1.minimum?
  match k with
  | none => True
  | some k => build_two_towers n k heights1 = build_two_towers n k heights2
  := sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval build_two_towers 8 38 [7, 8, 19, 7, 8, 7, 10, 20]

/-
info: 2
-/
-- #guard_msgs in
-- #eval build_two_towers 4 5 [2, 10, 4, 9]

/-
info: -1
-/
-- #guard_msgs in
-- #eval build_two_towers 3 10 [2, 3, 4]
-- </vc-theorems>
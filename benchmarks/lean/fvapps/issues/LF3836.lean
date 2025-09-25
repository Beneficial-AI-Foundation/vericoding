-- <vc-preamble>
def calcGame (gamemap : Matrix) : Nat := sorry

def rotateMatrix (m : Matrix) : Matrix := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getMinValue (gamemap : Matrix) : Nat :=
  gamemap.map (List.foldl min 0) |> List.foldl min 0
-- </vc-definitions>

-- <vc-theorems>
theorem gamemap_value_minimum {gamemap : Matrix} : 
  getMinValue gamemap ≤ calcGame gamemap := sorry

theorem gamemap_rotation_symmetry {gamemap : Matrix} :
  calcGame gamemap = calcGame (rotateMatrix gamemap) := sorry

theorem gamemap_monotonicity {gamemap : Matrix} {increased : Matrix} :
  (∀ i j, (gamemap.get! i).get! j + 1 = (increased.get! i).get! j) →
  calcGame gamemap ≤ calcGame increased := sorry

/-
info: 39
-/
-- #guard_msgs in
-- #eval calc [[1, 3, 9], [2, 8, 5], [5, 7, 4]]

/-
info: 560
-/
-- #guard_msgs in
-- #eval calc [[11, 72, 38], [80, 69, 65], [68, 96, 99]]

/-
info: 40
-/
-- #guard_msgs in
-- #eval calc [[1, 5, 1, 1], [1, 5, 5, 1], [5, 5, 5, 1], [1, 1, 5, 1]]
-- </vc-theorems>
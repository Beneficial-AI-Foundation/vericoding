def Point := List Int
def Points := List Point

instance : BEq Point where
  beq a b := a.zip b |>.all (fun (x, y) => x == y)

-- <vc-helpers>
-- </vc-helpers>

def countEqualDistances (points : Points) : Nat :=
  sorry

theorem count_always_nonnegative (points : Points) :
  countEqualDistances points ≥ 0 := sorry

theorem single_point_returns_zero (p : Point) :
  let points : Points := [p]
  countEqualDistances points = 0 := sorry

theorem points_on_line (x : Int) :
  let points : Points := [[x, 0], [x, 1], [x, 2], [x, 3], [x, 4]]
  countEqualDistances points = 10 := sorry

theorem permutation_invariant (points points' : Points) :
  points.length = points'.length →
  (∀ p, List.elem p points ↔ List.elem p points') →
  countEqualDistances points = countEqualDistances points' := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_equal_distances [[1, 1], [7, 5], [1, 5]]

/-
info: 11
-/
-- #guard_msgs in
-- #eval count_equal_distances [[0, 0], [0, 1], [0, 2], [-1, 1], [0, 1], [1, 1]]

/-
info: 33
-/
-- #guard_msgs in
-- #eval count_equal_distances [[46, -55], [46, 45], [46, 45], [83, -55], [46, 45], [83, -55], [46, 45], [83, 45], [83, 45], [46, -55]]

-- Apps difficulty: competition
-- Assurance level: guarded
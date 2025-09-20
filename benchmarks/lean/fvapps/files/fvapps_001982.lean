-- <vc-preamble>
def Point := List Int
def Points := List Point

instance : BEq Point where
  beq a b := a.zip b |>.all (fun (x, y) => x == y)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countEqualDistances (points : Points) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>
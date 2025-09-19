-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countEmptyParabolas (points : List (Int × Int)) : Nat :=
  sorry

def makeParabolaPoints (a h k : Int) (n : Nat) : List (Int × Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem countEmptyParabolas_nonnegative (points : List (Int × Int)) :
  countEmptyParabolas points ≥ 0 := by
  sorry

theorem countEmptyParabolas_single_point (point : Int × Int) :
  countEmptyParabolas [point] = 0 := by
  sorry

theorem countEmptyParabolas_through_parabola_points (a h k : Int) :
  a ≠ 0 →
  countEmptyParabolas (makeParabolaPoints a h k 5) ≥ 1 := by
  sorry

theorem countEmptyParabolas_duplicate_x_values (points : List (Int × Int)) :
  let deduped := points.foldl (fun acc (x, y) =>
    match acc.find? (fun (x', _) => x' = x) with
    | none => acc ++ [(x, y)]
    | some (x', y') =>
      if y > y'
      then acc.map (fun (x'', y'') => if x'' = x then (x, y) else (x'', y''))
      else acc
    ) []
  countEmptyParabolas points = countEmptyParabolas deduped := by
  sorry
-- </vc-theorems>
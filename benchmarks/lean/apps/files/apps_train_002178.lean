/-
Recently Vasya learned that, given two points with different $x$ coordinates, you can draw through them exactly one parabola with equation of type $y = x^2 + bx + c$, where $b$ and $c$ are reals. Let's call such a parabola an $U$-shaped one.

Vasya drew several distinct points with integer coordinates on a plane and then drew an $U$-shaped parabola through each pair of the points that have different $x$ coordinates. The picture became somewhat messy, but Vasya still wants to count how many of the parabolas drawn don't have any drawn point inside their internal area. Help Vasya.

The internal area of an $U$-shaped parabola is the part of the plane that lies strictly above the parabola when the $y$ axis is directed upwards.

-----Input-----

The first line contains a single integer $n$ ($1 \le n \le 100\,000$) — the number of points.

The next $n$ lines describe the points, the $i$-th of them contains two integers $x_i$ and $y_i$ — the coordinates of the $i$-th point. It is guaranteed that all points are distinct and that the coordinates do not exceed $10^6$ by absolute value.

-----Output-----

In the only line print a single integer — the number of $U$-shaped parabolas that pass through at least two of the given points and do not contain any of the given points inside their internal area (excluding the parabola itself).

-----Examples-----
Input
3
-1 0
0 2
1 0

Output
2

Input
5
1 0
1 -1
0 -1
-1 0
-1 -1

Output
1

-----Note-----

On the pictures below all $U$-shaped parabolas that pass through at least two given points are drawn for each of the examples. The $U$-shaped parabolas that do not have any given point inside their internal area are drawn in red.  [Image] The first example. 

 [Image] The second example.
-/

def countEmptyParabolas (points : List (Int × Int)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def makeParabolaPoints (a h k : Int) (n : Nat) : List (Int × Int) :=
  sorry

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

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_empty_parabolas [(-1, 0), (0, 2), (1, 0)]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_empty_parabolas [(1, 0), (1, -1), (0, -1), (-1, 0), (-1, -1)]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_empty_parabolas [(-751115, -925948)]

-- Apps difficulty: competition
-- Assurance level: guarded
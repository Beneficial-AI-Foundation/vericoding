/-
Taxis of Kharagpur are famous for making sharp turns. You are given the coordinates where a particular taxi was on a 2-D planes at N different moments: (x1, y1), (x2, y2), ..., (xN, yN). In between these coordinates, the taxi moves on a straight line. A turn at the i-th (2 ≤ i ≤ N-1) coordinate is said to be a sharp turn if the angle by which it turns at Point B = (xi, yi) when going from coordinates A = (xi-1, yi-1) to C = (xi+1, yi+1) via (xi, yi) is greater than 45 degrees. ie. suppose you extend the line segment AB further till a point D, then the angle DBC would be greater than 45 degrees.
You have to identify whether the taxi made a sharp turn somewhere or not (Please look at Output section for details). If it made a sharp turn, also identify whether it is possible to change the coordinates at one of the N moments to make sure that the taxi doesn't make any sharp turn. Note that all the N pairs of coordinates (including the new coordinates) should be integers and distinct and should have their x and y coordinates at least 0 and at most 50.

-----Input-----
- The first line of the input contains a single integer T denoting the number of test cases. The description of T test cases follows.
- The first line of each test case contains a single integer N denoting the number of moments at which you are given the information of the taxi's coordinates.
- Each of the next N lines contains two space-separated integers xi and yi denoting the x and y coordinates of the taxi at i-th moment.

-----Output-----
- For each test case, print a single line containing two space-separated strings, either of which can be a "yes" or "no" (without quotes). If there was no sharp turn, the first string should be "yes", and if there was a sharp turn, the first string should be "no". For the second string, you should tell whether it is possible to modify at most one coordinate in such a way that taxi doesn't make a sharp turn. Note that if the first string is "yes", then the second string would always be "yes".

-----Constraints-----
- 1 ≤ T ≤ 50
- 3 ≤ N ≤ 50
- 0 ≤ xi, yi ≤ 50
- It's guaranteed that all (xi, yi) pairs are distinct.

-----Example-----
Input
5
3
0 0
1 1
2 1
3
0 0
1 0
6 1
3
0 0
1 0
1 1
4
0 0
1 0
1 1
6 1
6
0 0
1 0
1 1
2 1
2 2
3 2

Output
yes yes
yes yes
no yes
no yes
no no

-----Explanation-----
Example 1. 

You can see that taxi is never making a sharp turn.

Example 3

You can see that taxi is making a sharp turn of 90 degrees, an angle greater than 45'. However, you can change the coordinates of the third points to (2, 1) to ensure that the angle remains <= 45'.
-/

-- <vc-helpers>
-- </vc-helpers>

def solveTaxiTurns (coords : List (List Int)) : Option String := sorry

theorem result_is_valid (coords : List (List Int)) :
  match solveTaxiTurns coords with
  | none => True
  | some result => result = "yes yes" ∨ result = "no yes" ∨ result = "no no" := sorry

theorem two_points_yes_yes (p1 p2 : List Int) :
  solveTaxiTurns [p1, p2] = some "yes yes" := sorry

theorem yes_yes_implies_no_sharp_angles (coords : List (List Int)) (i : Nat) :
  solveTaxiTurns coords = some "yes yes" →
  i + 2 < coords.length →
  let p1 := coords[i]!
  let p2 := coords[i+1]!
  let p3 := coords[i+2]!
  let dx1 := p2[0]! - p1[0]!
  let dy1 := p2[1]! - p1[1]!
  let dx2 := p3[0]! - p2[0]!
  let dy2 := p3[1]! - p2[1]!
  let dot := dx1 * dx2 + dy1 * dy2
  let mag1 := Float.sqrt (Float.ofInt (dx1 * dx1 + dy1 * dy1))
  let mag2 := Float.sqrt (Float.ofInt (dx2 * dx2 + dy2 * dy2))
  let cosTheta := Float.ofInt dot / (mag1 * mag2)
  let angle := Float.acos (min 1 (max (-1) cosTheta))
  dx1 * dx1 + dy1 * dy1 > 0 ∧ dx2 * dx2 + dy2 * dy2 > 0 →
  angle ≤ 0.7853981633974483 + 0.00001 := sorry  -- π/4 as decimal

theorem same_points_is_none (x y : Int) :
  solveTaxiTurns [[x,y], [x,y]] = none := sorry

theorem coords_in_bounds (coords : List (List Int)) :
  solveTaxiTurns coords ≠ none →
  ∀ point ∈ coords, ∀ coord ∈ point, 0 ≤ coord ∧ coord ≤ 50 := sorry

/-
info: 'yes yes'
-/
-- #guard_msgs in
-- #eval solve_taxi_turns [[0, 0], [1, 1], [2, 1]]

/-
info: 'no yes'
-/
-- #guard_msgs in
-- #eval solve_taxi_turns [[0, 0], [1, 0], [1, 1]]

/-
info: 'no no'
-/
-- #guard_msgs in
-- #eval solve_taxi_turns [[0, 0], [1, 0], [1, 1], [2, 1], [2, 2], [3, 2]]

-- Apps difficulty: interview
-- Assurance level: unguarded
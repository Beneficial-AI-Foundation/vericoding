-- <vc-preamble>
def Point := (Int × Int)
def Triangle := (Point × Point × Point)
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def area (t : Triangle) : Float := sorry
def find_biggTriang (pts : List Point) : (Nat × Nat × Nat × List Triangle × Float) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_biggTriang_result_length 
  (pts : List Point) : 
  let result := find_biggTriang pts
  List.length [result.1, result.2.1, result.2.2.1, result.2.2.2.1.length, 1] = 5 := sorry

theorem find_biggTriang_point_count 
  (pts : List Point) :
  let result := find_biggTriang pts
  result.1 = pts.length := sorry

theorem find_biggTriang_triangle_count
  (pts : List Point) :
  let result := find_biggTriang pts
  let n := pts.length
  result.2.1 = n * (n-1) * (n-2) / 6 := sorry

theorem find_biggTriang_nonzero_area_count
  (pts : List Point) :
  let result := find_biggTriang pts 
  0 ≤ result.2.2.1 ∧ result.2.2.1 ≤ result.2.1 := sorry

theorem find_biggTriang_max_area_nonneg
  (pts : List Point) :
  let result := find_biggTriang pts
  result.2.2.2.2 ≥ 0 := sorry

theorem area_cyclic_permutation
  (p1 p2 p3 : Point) :
  let t1 := (p1, p2, p3)
  let t2 := (p2, p3, p1) 
  let t3 := (p3, p1, p2)
  (area t1 - area t2).abs < 1e-10 ∧ (area t2 - area t3).abs < 1e-10 := sorry

/-
info: [19, 969, 953, [[0, 1], [7, 10], [10, 0]], 48.5]
-/
-- #guard_msgs in
-- #eval find_biggTriang [(0, 1), (7, 3), (9, 0), (7, 10), (2, 9), (10, 7), (2, 8), (9, 8), (4, 4), (2, 10), (10, 1), (0, 4), (4, 3), (10, 0), (0, 3), (3, 4), (1, 1), (7, 2), (4, 0)]

/-
info: [15, 455, 446, [[[0, 0], [9, 10], [10, 0]], [[0, 0], [10, 0], [3, 10]]], 50.0]
-/
-- #guard_msgs in
-- #eval find_biggTriang [(7, 4), (0, 0), (9, 10), (5, 0), (8, 1), (7, 6), (9, 3), (2, 4), (6, 3), (5, 6), (3, 6), (10, 0), (9, 7), (3, 10), (10, 2)]

/-
info: [3, 1, 1, [[0, 0], [3, 0], [0, 4]], 6.0]
-/
-- #guard_msgs in
-- #eval find_biggTriang [(0, 0), (3, 0), (0, 4)]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
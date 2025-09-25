-- <vc-preamble>
def Point := (Int × Int)
def Triangle := (Point × Point × Point)
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>
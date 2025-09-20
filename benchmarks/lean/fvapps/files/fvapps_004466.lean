-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hyperrectangularity_properties : List α → Option (List Nat) := sorry

theorem hyperrectangularity_2d_rectangular {rows cols : Nat} 
  (h1 : 0 < rows) (h2 : rows ≤ 5)
  (h3 : 0 < cols) (h4 : cols ≤ 5)
  (arr : List (List Nat)) 
  (h5 : arr = List.map (fun j => List.map (fun i => i + j*cols) (List.range cols)) (List.range rows))
  : hyperrectangularity_properties arr = some [rows, cols] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hyperrectangularity_1d {arr : List α}
  : hyperrectangularity_properties arr = 
    if arr.isEmpty then some [0] else some [arr.length] := sorry

theorem hyperrectangularity_3d {x y z : Nat}
  (h1 : 0 < x) (h2 : x ≤ 3)
  (h3 : 0 < y) (h4 : y ≤ 3)  
  (h5 : 0 < z) (h6 : z ≤ 3)
  (arr : List (List (List Nat)))
  (h7 : arr = List.map (fun i => 
          List.map (fun j =>
            List.map (fun k => k + j*z + i*y*z) (List.range z)) 
          (List.range y))
        (List.range x))
  : hyperrectangularity_properties arr = some [x, y, z] := sorry

theorem hyperrectangularity_empty 
  : hyperrectangularity_properties ([] : List α) = some [0] := sorry

theorem hyperrectangularity_non_rectangular
  (arr : List (List Nat))
  (h : arr = [[1,2], [1]])
  : hyperrectangularity_properties arr = none := sorry
-- </vc-theorems>
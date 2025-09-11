-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_subway_fare (n : Nat) (m : Nat) (edges : List (Nat × Nat × Nat)) : Int := sorry

theorem subway_fare_type_and_range {n : Nat} {m : Nat} {edges : List (Nat × Nat × Nat)}
    (h : n ≥ 2) :
    let result := solve_subway_fare n m edges
    result ≥ -1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem subway_fare_no_edges {n : Nat} {m : Nat} 
    (h : m = 0) :
    solve_subway_fare n m [] = -1 := sorry

theorem subway_fare_single_node {m : Nat} {edges : List (Nat × Nat × Nat)} :
    solve_subway_fare 1 m edges = 0 := sorry

theorem subway_fare_result_bounds {n : Nat} {m : Nat} {edges : List (Nat × Nat × Nat)}
    (h : n ≥ 2) :
    let result := solve_subway_fare n m edges
    (result = -1 ∨ result ≥ 0) := sorry

theorem subway_fare_max_cost {n : Nat} {m : Nat} {edges : List (Nat × Nat × Nat)}
    (h₁ : n ≥ 2)
    (h₂ : solve_subway_fare n m edges ≠ -1) :
    solve_subway_fare n m edges ≤ m := sorry

theorem subway_fare_single_edge :
    solve_subway_fare 2 1 [(1,2,1)] = 1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_subway_fare 3 3 [(1, 2, 1), (2, 3, 1), (3, 1, 2)]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_subway_fare 8 11 [(1, 3, 1), (1, 4, 2), (2, 3, 1), (2, 5, 1), (3, 4, 3), (3, 6, 3), (3, 7, 3), (4, 8, 4), (5, 6, 1), (6, 7, 5), (7, 8, 5)]

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_subway_fare 2 0 []
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded
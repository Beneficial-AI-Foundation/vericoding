-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>
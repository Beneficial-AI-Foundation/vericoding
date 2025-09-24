-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_hotel_path (hotels : List Nat) (L : Nat) (queries : List (Nat × Nat)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hotel_path_basic_test (h : hotels = [1, 3, 6]) (l : L = 3) :
  solve_hotel_path hotels L [(1, 3)] = [2] :=
  sorry

theorem hotel_path_symmetric (h : hotels = [1, 3, 6]) (l : L = 3) :
  solve_hotel_path hotels L [(1, 3)] = solve_hotel_path hotels L [(3, 1)] :=
  sorry

theorem hotel_path_self (h : hotels = [1, 3, 6]) (l : L = 3) :
  solve_hotel_path hotels L [(1, 1)] = [0] :=
  sorry

theorem hotel_path_output_positive (h : hotels = [1, 3, 6, 10]) (l : L = 4) :
  let result := solve_hotel_path hotels L [(1, 4), (2, 3)]
  ∀ x ∈ result, x ≥ 0 :=
  sorry

theorem hotel_path_output_length (h : hotels = [1, 3, 6, 10]) (l : L = 4) :
  let result := solve_hotel_path hotels L [(1, 4), (2, 3)]
  result.length = 2 :=
  sorry
-- </vc-theorems>
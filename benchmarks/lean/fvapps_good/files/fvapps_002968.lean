-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chess_triangle (n m : Int) : Int := sorry

theorem zero_dimensions :
  chess_triangle 0 1 = 0 ∧ 
  chess_triangle 1 0 = 0 ∧ 
  chess_triangle 0 0 = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tiny_boards :
  ∀ n m, n < 2 → m < 2 → chess_triangle n m = 0 := sorry
-- </vc-theorems>
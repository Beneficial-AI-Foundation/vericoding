-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_make_square (a1 b1 a2 b2 : Nat) : Bool := sorry

theorem can_make_square_symmetric_first_rect (a1 b1 a2 b2 : Nat) 
  (h1 : a1 > 0) (h2 : b1 > 0) (h3 : a2 > 0) (h4 : b2 > 0) :
  can_make_square a1 b1 a2 b2 = can_make_square b1 a1 a2 b2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_make_square_symmetric_second_rect (a1 b1 a2 b2 : Nat)
  (h1 : a1 > 0) (h2 : b1 > 0) (h3 : a2 > 0) (h4 : b2 > 0) :
  can_make_square a1 b1 a2 b2 = can_make_square a1 b1 b2 a2 := sorry

theorem can_make_square_symmetric_swap_rects (a1 b1 a2 b2 : Nat)
  (h1 : a1 > 0) (h2 : b1 > 0) (h3 : a2 > 0) (h4 : b2 > 0) :
  can_make_square a1 b1 a2 b2 = can_make_square a2 b2 a1 b1 := sorry

theorem can_make_square_identical_rects_false (n : Nat) (h : n > 0) :
  can_make_square n n n n = false := sorry

theorem can_make_square_known_case1 :
  can_make_square 2 3 3 1 = true := sorry

theorem can_make_square_known_case2 :
  can_make_square 3 2 1 3 = true := sorry

theorem can_make_square_known_case3 :
  can_make_square 3 3 1 3 = false := sorry
-- </vc-theorems>
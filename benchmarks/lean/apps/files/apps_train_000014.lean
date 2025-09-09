/-
Vasya claims that he had a paper square. He cut it into two rectangular parts using one vertical or horizontal cut. Then Vasya informed you the dimensions of these two rectangular parts. You need to check whether Vasya originally had a square. In other words, check if it is possible to make a square using two given rectangles.

-----Input-----

The first line contains an integer $t$ ($1 \le t \le 10^4$) — the number of test cases in the input. Then $t$ test cases follow.

Each test case is given in two lines.

The first line contains two integers $a_1$ and $b_1$ ($1 \le a_1, b_1 \le 100$) — the dimensions of the first one obtained after cutting rectangle. The sizes are given in random order (that is, it is not known which of the numbers is the width, and which of the numbers is the length).

The second line contains two integers $a_2$ and $b_2$ ($1 \le a_2, b_2 \le 100$) — the dimensions of the second obtained after cutting rectangle. The sizes are given in random order (that is, it is not known which of the numbers is the width, and which of the numbers is the length).

-----Output-----

Print $t$ answers, each of which is a string "YES" (in the case of a positive answer) or "NO" (in the case of a negative answer). The letters in words can be printed in any case (upper or lower).

-----Example-----
Input
3
2 3
3 1
3 2
1 3
3 3
1 3

Output
Yes
Yes
No
-/

-- <vc-helpers>
-- </vc-helpers>

def can_make_square (a1 b1 a2 b2 : Nat) : Bool := sorry

theorem can_make_square_symmetric_first_rect (a1 b1 a2 b2 : Nat) 
  (h1 : a1 > 0) (h2 : b1 > 0) (h3 : a2 > 0) (h4 : b2 > 0) :
  can_make_square a1 b1 a2 b2 = can_make_square b1 a1 a2 b2 := sorry

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

/-
info: True
-/
-- #guard_msgs in
-- #eval can_make_square 2 3 3 1

/-
info: True
-/
-- #guard_msgs in
-- #eval can_make_square 3 2 1 3

/-
info: False
-/
-- #guard_msgs in
-- #eval can_make_square 3 3 1 3

-- Apps difficulty: interview
-- Assurance level: unguarded
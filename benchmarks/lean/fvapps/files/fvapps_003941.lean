-- <vc-preamble>
def findSquares (x y : Nat) : Nat := sorry

-- Result should be non-negative
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_squares (n : Nat) : Nat :=
  Nat.rec 0 (fun k res => res + k*k) n
-- </vc-definitions>

-- <vc-theorems>
theorem findSquares_nonneg (x y : Nat) : 
  findSquares x y ≥ 0 := sorry

-- For 0 dimensions, result should be 0  

theorem findSquares_zero (x y : Nat) :
  x = 0 ∨ y = 0 → findSquares x y = 0 := sorry

-- Result should be x*y for 1xN rectangles

theorem findSquares_stripe (x y : Nat) :
  y = 1 → findSquares x y = x := sorry

-- For a square, result should be sum of squares from 1 to side length

theorem findSquares_square (n : Nat) : 
  findSquares n n = sum_squares n := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval findSquares 3 2

/-
info: 20
-/
-- #guard_msgs in
-- #eval findSquares 4 3

/-
info: 100
-/
-- #guard_msgs in
-- #eval findSquares 11 4
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded
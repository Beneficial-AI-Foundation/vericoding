-- <vc-preamble>
def sum_squares (n : Nat) : Nat :=
  Nat.rec 0 (fun k res => res + k*k) n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findSquares (x y : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem findSquares_nonneg (x y : Nat) :
  findSquares x y ≥ 0 :=
sorry

theorem findSquares_zero (x y : Nat) :
  x = 0 ∨ y = 0 → findSquares x y = 0 :=
sorry

theorem findSquares_stripe (x y : Nat) :
  y = 1 → findSquares x y = x :=
sorry

theorem findSquares_square (n : Nat) :
  findSquares n n = sum_squares n :=
sorry
-- </vc-theorems>
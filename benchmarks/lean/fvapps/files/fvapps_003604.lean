-- <vc-preamble>
def iterateN (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => iterateN f n (f x)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_the_ball (start : Nat) (swaps : List (Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_the_ball_no_swaps (start : Nat) :
  find_the_ball start [] = start :=
sorry
-- </vc-theorems>
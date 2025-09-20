-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def divisible_count (x : Nat) (y : Nat) (k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem divisible_count_zero_width (x k : Nat) (h : k > 0) :
  divisible_count x (x-1) k = 0 :=
  sorry

theorem divisible_count_step (x y k : Nat) (h : k > 0) (h2 : (y + 1) % k = 0) :
  divisible_count x (y + k) k = divisible_count x y k + 1 :=
  sorry

theorem divisible_count_periodic (x k : Nat) (h : k > 0) :
  divisible_count x (x + k - 1) k = divisible_count (x + k) (x + 2*k - 1) k :=
  sorry
-- </vc-theorems>
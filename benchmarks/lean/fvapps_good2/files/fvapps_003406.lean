-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def doors (n : Nat) : Nat :=
sorry

def sqrt (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem doors_non_negative (n : Nat) :
  doors n ≥ 0 :=
sorry

theorem doors_squared_leq (n : Nat) :
  (doors n) * (doors n) ≤ n :=
sorry

theorem doors_plus_one_squared_gt (n : Nat) :
  (doors n + 1) * (doors n + 1) > n :=
sorry

theorem doors_perfect_squares (n : Nat) :
  doors (n * n) = n :=
sorry
-- </vc-theorems>
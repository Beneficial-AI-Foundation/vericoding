-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortest_time (n m : Nat) (speeds : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_non_negative (n m : Nat) (speeds : List Nat) :
  shortest_time n m speeds ≥ 0 :=
  sorry

theorem floor_one_is_zero (m : Nat) (speeds : List Nat) :
  shortest_time 1 m speeds = 0 :=
  sorry

theorem elevator_not_worse_than_walking (n m : Nat) (speeds : List Nat) (h: speeds.length > 3) :
  n > 1 →
  shortest_time n m speeds ≤ (n-1) * (speeds.get! 3) :=
  sorry

theorem same_floor_elevator_time (n : Nat) (speeds : List Nat) (h: speeds.length > 3) :
  n > 1 →
  shortest_time n n speeds = min 
    (speeds.get! 1 + speeds.get! 2 + (n-1)*speeds.get! 0 + speeds.get! 1) 
    ((n-1)*speeds.get! 3) :=
  sorry

theorem extreme_walking_speeds (n m : Nat) (speeds : List Nat) (h: speeds.length > 3) :
  shortest_time n m speeds = min 
    (Nat.sub (max m n) (min m n)*speeds.get! 0 + speeds.get! 1 + speeds.get! 2 + (n-1)*speeds.get! 0 + speeds.get! 1) 
    ((n-1)*speeds.get! 3) :=
  sorry
-- </vc-theorems>
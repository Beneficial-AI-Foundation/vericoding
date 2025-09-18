-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def flipLights (n : Nat) (m : Nat) : Nat :=
  sorry

-- Output should be between 1 and 4 positions
-- </vc-definitions>

-- <vc-theorems>
theorem output_range (n m : Nat) : 
  n > 0 → 
  1 ≤ flipLights n m ∧ 
  flipLights n m ≤ min 16 (2 ^ (min n 4)) :=
sorry

-- Zero operations should result in one possible state

theorem zero_operations (n : Nat) :
  n > 0 →
  flipLights n 0 = 1 :=
sorry

-- Result should stabilize for large m

theorem operation_stabilization (n : Nat) :
  n > 0 →
  flipLights n 1000 = flipLights n 1001 :=
sorry

-- More lights should never decrease possible states

theorem monotonic_n (n m : Nat) :
  n > 1 →
  flipLights (n-1) m ≤ flipLights n m :=
sorry
-- </vc-theorems>
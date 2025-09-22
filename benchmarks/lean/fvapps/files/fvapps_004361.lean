-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Ackermann : Nat → Nat → Option Nat 
| m, n => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ack_m0_property (n : Nat) :
  Ackermann 0 n = some (n + 1) :=
sorry
-- </vc-theorems>
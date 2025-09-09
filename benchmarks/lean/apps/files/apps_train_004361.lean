-- <vc-helpers>
-- </vc-helpers>

def Ackermann : Nat → Nat → Option Nat 
| m, n => sorry

theorem ack_m0_property (n : Nat) :
  Ackermann 0 n = some (n + 1) :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
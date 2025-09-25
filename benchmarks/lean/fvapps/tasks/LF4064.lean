-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getParticipants (h : Nat) : Nat :=
  sorry

def choose (n k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem handshakes_bounds (h : Nat) :
  let n := getParticipants h
  let possibleHandshakes := if n ≥ 2 then choose n 2 else 0
  n ≥ 1 ∧ possibleHandshakes ≥ h :=
sorry

theorem basic_cases :
  getParticipants 0 = 1 ∧
  getParticipants 1 = 2 ∧
  getParticipants 6 = 4 :=
sorry
-- </vc-theorems>
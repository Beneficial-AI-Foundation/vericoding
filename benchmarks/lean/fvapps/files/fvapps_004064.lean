-- <vc-preamble>
def getParticipants (h : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
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

/-
info: 1
-/
-- #guard_msgs in
-- #eval get_participants 0

/-
info: 2
-/
-- #guard_msgs in
-- #eval get_participants 1

/-
info: 4
-/
-- #guard_msgs in
-- #eval get_participants 6
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded
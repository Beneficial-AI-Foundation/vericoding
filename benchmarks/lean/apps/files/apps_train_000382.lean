def MOD := 1000000007

def count_char (s : String) (c : Char) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def numWays (s : String) : Nat :=
  sorry

theorem numWays_non_negative (s : String) :
  numWays s ≥ 0 :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval numWays "10101"

/-
info: 0
-/
-- #guard_msgs in
-- #eval numWays "1001"

/-
info: 3
-/
-- #guard_msgs in
-- #eval numWays "0000"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
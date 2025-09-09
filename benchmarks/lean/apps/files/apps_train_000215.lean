-- <vc-helpers>
-- </vc-helpers>

def longestWPI (hours : List Nat) : Nat := sorry

theorem longestWPI_non_negative (hours : List Nat) : 
  longestWPI hours ≥ 0 := sorry

theorem longestWPI_bounded (hours : List Nat) :
  longestWPI hours ≤ hours.length := sorry

theorem longestWPI_empty :
  longestWPI [] = 0 := sorry

theorem longestWPI_optimal (hours : List Nat) (start len : Nat) :
  start < hours.length →
  len > longestWPI hours →
  len ≤ hours.length - start →
  let subseq := (hours.drop start).take len
  let productive := (subseq.filter (· > 8)).length 
  let tired := len - productive
  productive ≤ tired := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval longestWPI [9, 9, 6, 0, 6, 6, 9]

/-
info: 0
-/
-- #guard_msgs in
-- #eval longestWPI [6, 6, 6]

/-
info: 3
-/
-- #guard_msgs in
-- #eval longestWPI [9, 9, 9]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
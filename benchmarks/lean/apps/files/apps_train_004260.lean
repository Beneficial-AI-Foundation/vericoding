-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def points (games : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem points_draws (n : Nat) :
  let draw_games := List.map (fun i => s!"{i}:{i}") (List.range n)
  points draw_games = n :=
  sorry

theorem points_wins (nums : List Nat) :
  let win_games := List.map (fun n => s!"{n+1}:{n}") nums
  points win_games = nums.length * 3 :=
  sorry

/-
info: 30
-/
-- #guard_msgs in
-- #eval points ["1:0", "2:0", "3:0", "4:0", "2:1", "3:1", "4:1", "3:2", "4:2", "4:3"]

/-
info: 10
-/
-- #guard_msgs in
-- #eval points ["1:1", "2:2", "3:3", "4:4", "2:2", "3:3", "4:4", "3:3", "4:4", "4:4"]

/-
info: 0
-/
-- #guard_msgs in
-- #eval points ["0:1", "0:2", "0:3", "0:4", "1:2", "1:3", "1:4", "2:3", "2:4", "3:4"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
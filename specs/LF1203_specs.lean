-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_race_end (n : Nat) (team_a : List Int) (team_b : List Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_race_end_returns_valid_answer
  {n : Nat} {team_a team_b : List Int}
  (h1 : team_a.length = n)
  (h2 : team_b.length = n)
  (h3 : n > 0) :
  can_race_end n team_a team_b = "YES" ∨ can_race_end n team_a team_b = "NO" :=
  sorry

theorem can_race_end_equal_max_implies_no
  {n : Nat} {team_a team_b : List Int}
  (h1 : team_a.length = n)
  (h2 : team_b.length = n)
  (h3 : n > 0)
  (h4 : List.maximum? team_a = List.maximum? team_b) :
  can_race_end n team_a team_b = "NO" :=
  sorry

theorem can_race_end_unequal_max_implies_yes
  {n : Nat} {team_a team_b : List Int}
  (h1 : team_a.length = n)
  (h2 : team_b.length = n)
  (h3 : n > 0)
  (h4 : List.maximum? team_a ≠ List.maximum? team_b) :
  can_race_end n team_a team_b = "YES" :=
  sorry

theorem can_race_end_single_element_equal
  (speed : Int) :
  can_race_end 1 [speed] [speed] = "NO" :=
  sorry

theorem can_race_end_single_element_greater
  (speed : Int) :
  can_race_end 1 [speed + 1] [speed] = "YES" :=
  sorry

theorem can_race_end_equal_max_extension
  {team : List Int} {max_speed : Int}
  (h1 : team.length > 0) :
  can_race_end (team.length + 1) (team ++ [max_speed]) (team ++ [max_speed]) = "NO" :=
  sorry

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval can_race_end 5 [1, 2, 3, 4, 5] [2, 7, 8, 9, 9]

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval can_race_end 3 [1, 2, 5] [3, 4, 5]

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval can_race_end 1 [3] [5]
-- </vc-theorems>
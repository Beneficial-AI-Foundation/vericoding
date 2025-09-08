/-
In some ranking people collects points. The challenge is sort by points and calulate position for every person. But remember if two or more persons have same number of points, they should have same position number and sorted by name (name is unique).

For example:
Input structure:

Output should be:
-/

-- <vc-helpers>
-- </vc-helpers>

def ranking (players : List Player) : List Player :=
  sorry

theorem ranking_length_preservation (players : List Player) :
  (ranking players).length = players.length :=
  sorry

theorem ranking_min_position (players : List Player) :
  players ≠ [] → 
  (List.map Player.position (ranking players)).head! > 0 ∧
  (List.map Player.position (ranking players)).head! ≤ 1 :=
  sorry

theorem ranking_equal_points_equal_position (players : List Player) :
  ∀ i : Nat, i + 1 < (ranking players).length →
    let result := ranking players
    (result[i]!.points = result[i+1]!.points) →
    (result[i]!.position = result[i+1]!.position) :=
  sorry

theorem ranking_points_position_relation (players : List Player) :
  ∀ i : Nat, i + 1 < (ranking players).length →
    let result := ranking players
    (result[i]!.points > result[i+1]!.points) →
    (result[i]!.position < result[i+1]!.position) :=
  sorry

theorem ranking_points_descending (players : List Player) :
  ∀ i : Nat, i + 1 < (ranking players).length →
    let result := ranking players
    result[i]!.points ≥ result[i+1]!.points :=
  sorry

theorem ranking_names_ascending_same_points (players : List Player) :
  ∀ i : Nat, i + 1 < (ranking players).length →
    let result := ranking players
    result[i]!.points = result[i+1]!.points →
    result[i]!.name ≤ result[i+1]!.name :=
  sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval ranking []

-- Apps difficulty: introductory
-- Assurance level: guarded
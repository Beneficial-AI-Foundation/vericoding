-- <vc-preamble>
def maxList (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => List.foldl (fun acc y => max acc y) x xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_dungeon_game (monsters : List Nat) (heroes : List Hero) : Nat := sorry

theorem dungeon_game_basic_properties
  (monsters : List Nat) (heroes : List Hero)
  (h1 : monsters.length > 0)
  (h2 : heroes.length > 0)
  (h3 : ∀ m ∈ monsters, m ≥ 1 ∧ m ≤ 1000)
  (h4 : ∀ h ∈ heroes, h.power ≥ 1 ∧ h.power ≤ 1000 ∧ h.endurance ≥ 1 ∧ h.endurance ≤ 1000) :
  let result := solve_dungeon_game monsters heroes
  (result = 0 ∨ result ≥ 1) ∧
  (result ≠ 0 → (
    (∃ h ∈ heroes, h.power ≥ maxList monsters) ∧
    result ≤ monsters.length
  )) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dungeon_game_weak_monsters
  (monsters : List Nat)
  (heroes : List Hero)
  (h1 : monsters.length > 0)
  (h2 : heroes.length > 0)
  (h3 : ∀ m ∈ monsters, m = 1)
  (h4 : ∀ h ∈ heroes, h.power = 2 ∧ h.endurance = 1) :
  solve_dungeon_game monsters heroes = monsters.length := sorry

theorem dungeon_game_super_hero
  (monsters : List Nat)
  (hero_endurance : Nat)
  (h1 : monsters.length > 0)
  (h2 : ∀ m ∈ monsters, m ≥ 1 ∧ m ≤ 10)
  (h3 : hero_endurance ≥ 1) :
  let max_monster := maxList monsters
  let heroes := [Hero.mk (max_monster + 1) hero_endurance]
  let result := solve_dungeon_game monsters heroes
  (if hero_endurance ≥ monsters.length
   then result = 1
   else result = (monsters.length + hero_endurance - 1) / hero_endurance) := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_dungeon_game [2, 3, 11, 14, 1, 8] [(3, 2), (100, 1)]

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_dungeon_game [3, 5, 100, 2, 3] [(30, 5), (90, 1)]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_dungeon_game [1, 2, 3] [(5, 3)]
-- </vc-theorems>
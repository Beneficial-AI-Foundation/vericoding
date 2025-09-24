-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_damage (your_type: PokemonType) (opponent_type: PokemonType) (attack: Nat) (defense: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem damage_always_positive (your_type: PokemonType) (opponent_type: PokemonType) 
    (attack: Nat) (defense: Nat) (h1: attack > 0) (h2: defense > 0) :
  calculate_damage your_type opponent_type attack defense > 0 :=
sorry

theorem damage_decreases_with_defense (your_type: PokemonType) (opponent_type: PokemonType)
    (attack: Nat) (defense1 defense2: Nat) (h1: defense1 < defense2) :
  calculate_damage your_type opponent_type attack defense1 ≥ 
  calculate_damage your_type opponent_type attack defense2 :=
sorry

theorem damage_increases_with_attack (your_type: PokemonType) (opponent_type: PokemonType)
    (attack1 attack2: Nat) (defense: Nat) (h1: attack1 < attack2) :
  calculate_damage your_type opponent_type attack1 defense ≤
  calculate_damage your_type opponent_type attack2 defense :=
sorry

/-
info: 25
-/
-- #guard_msgs in
-- #eval calculate_damage "fire" "water" 100 100

/-
info: 100
-/
-- #guard_msgs in
-- #eval calculate_damage "grass" "water" 100 100

/-
info: 50
-/
-- #guard_msgs in
-- #eval calculate_damage "electric" "fire" 100 100
-- </vc-theorems>
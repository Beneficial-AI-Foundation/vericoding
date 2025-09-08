/-
It's a Pokemon battle! Your task is to calculate the damage that a particular move would do using the following formula (not the actual one from the game):

Where:

* attack = your attack power
* defense = the opponent's defense
* effectiveness = the effectiveness of the attack based on the matchup (see explanation below)

Effectiveness:

Attacks can be super effective, neutral, or not very effective depending on the matchup. For example, water would be super effective against fire, but not very effective against grass.

* Super effective: 2x damage
* Neutral: 1x damage
* Not very effective: 0.5x damage

To prevent this kata from being tedious, you'll only be dealing with four types: `fire`, `water`, `grass`, and `electric`.  Here is the effectiveness of each matchup:

* `fire > grass`
* `fire < water`
* `fire = electric`

* `water < grass`
* `water < electric`

* `grass = electric`

For this kata, any type against itself is not very effective. Also, assume that the relationships between different types are symmetric (if `A` is super effective against `B`, then `B` is not very effective against `A`).

The function you must implement takes in:
1. your type
2. the opponent's type
3. your attack power
4. the opponent's defense
-/

-- <vc-helpers>
-- </vc-helpers>

def calculate_damage (your_type: PokemonType) (opponent_type: PokemonType) (attack: Nat) (defense: Nat) : Nat :=
  sorry

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

-- Apps difficulty: introductory
-- Assurance level: unguarded
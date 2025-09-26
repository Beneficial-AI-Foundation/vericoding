-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fight (r1 r2 : Robot) (t : Tactics) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fight_returns_valid_result (r1 r2 : Robot) (t : Tactics) :
  let result := fight r1 r2 t
  (result = s!"{r1.name} has won the fight." ∨ 
   result = s!"{r2.name} has won the fight." ∨
   result = "The fight was a draw.") :=
sorry

theorem faster_robot_attacks_first (r1 r2 : Robot) (t : Tactics) :
  r1.speed ≠ r2.speed →
  r1.tactics ≠ [] →
  r2.tactics ≠ [] →
  let faster := if r1.speed > r2.speed then r1 else r2
  let slower := if r1.speed > r2.speed then r2 else r1
  let firstDamage := match faster.tactics.head? with
    | none => 0 
    | some tactic => match t.val.lookup tactic with
      | none => 0
      | some dmg => dmg
  firstDamage ≥ slower.health →
  fight r1 r2 t = s!"{faster.name} has won the fight." :=
sorry

theorem equal_health_no_tactics_draws (r1 r2 : Robot) (t : Tactics) :
  r1.health = r2.health →
  r1.tactics = [] →
  r2.tactics = [] →
  fight r1 r2 t = "The fight was a draw." :=
sorry

/-
info: 'Missile Bob has won the fight.'
-/
-- #guard_msgs in
-- #eval fight {"name": "Rocky", "health": 100, "speed": 20, "tactics": ["punch", "punch", "laser", "missile"]} {"name": "Missile Bob", "health": 100, "speed": 21, "tactics": ["missile", "missile", "missile", "missile"]} {"punch": 20, "laser": 30, "missile": 35}

/-
info: 'The fight was a draw.'
-/
-- #guard_msgs in
-- #eval fight {"name": "Bot1", "health": 100, "speed": 20, "tactics": ["punch"]} {"name": "Bot2", "health": 100, "speed": 20, "tactics": ["punch"]} tactics
-- </vc-theorems>
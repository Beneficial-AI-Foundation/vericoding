-- <vc-preamble>
def Month := String
def Day := String
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BehaviorMap := List (Month × List (Day × BehaviorType))

def naughty_or_nice (behaviors: BehaviorMap) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem naughty_or_nice_returns_valid_result (behaviors: BehaviorMap) :
  naughty_or_nice behaviors = "Nice!" ∨ naughty_or_nice behaviors = "Naughty!" :=
sorry

theorem naughty_or_nice_matches_count (behaviors: BehaviorMap) :
  let nice_count := behaviors.foldl (fun acc m => 
    acc + m.2.foldl (fun inner_acc d => 
      inner_acc + match d.2 with
      | BehaviorType.Nice => 1
      | BehaviorType.Naughty => -1) 0) 0
  naughty_or_nice behaviors = if nice_count >= 0 then "Nice!" else "Naughty!" :=
sorry

theorem all_nice_returns_nice (behaviors: BehaviorMap) 
  (h: behaviors.all (fun m => 
      m.2.all (fun d => match d.2 with
        | BehaviorType.Nice => true
        | BehaviorType.Naughty => false))) :
  naughty_or_nice behaviors = "Nice!" :=
sorry

/-
info: 'Nice!'
-/
-- #guard_msgs in
-- #eval naughty_or_nice {"January": {"1": "Nice", "2": "Naughty", "3": "Nice"}, "February": {"1": "Naughty", "2": "Nice", "3": "Naughty"}}

/-
info: 'Nice!'
-/
-- #guard_msgs in
-- #eval naughty_or_nice {"January": {"1": "Nice", "2": "Nice", "3": "Nice"}, "February": {"1": "Nice", "2": "Nice", "3": "Nice"}}

/-
info: 'Naughty!'
-/
-- #guard_msgs in
-- #eval naughty_or_nice {"January": {"1": "Naughty", "2": "Naughty", "3": "Naughty"}, "February": {"1": "Naughty", "2": "Naughty", "3": "Naughty"}}
-- </vc-theorems>
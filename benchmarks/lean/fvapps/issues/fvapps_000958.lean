-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def race_winner (finish : Float) (distance_to_bolt : Float) (tiger_acceleration : Float) (bolt_speed : Float) : String := sorry

theorem race_winner_returns_valid_result (finish : Float) (distance_to_bolt : Float) (tiger_acceleration : Float) (bolt_speed : Float)
    (h1 : finish > 0) 
    (h2 : distance_to_bolt > 0)
    (h3 : tiger_acceleration > 0)
    (h4 : bolt_speed > 0) :
    (race_winner finish distance_to_bolt tiger_acceleration bolt_speed = "Bolt" ∨
     race_winner finish distance_to_bolt tiger_acceleration bolt_speed = "Tiger") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem race_winner_correct_winner (finish : Float) (distance_to_bolt : Float) (tiger_acceleration : Float) (bolt_speed : Float)
    (h1 : finish > 0)
    (h2 : distance_to_bolt > 0)
    (h3 : tiger_acceleration > 0) 
    (h4 : bolt_speed > 0) :
    let tiger_time := Float.sqrt (2 * (finish + distance_to_bolt) / tiger_acceleration);
    let bolt_time := finish / bolt_speed;
    (race_winner finish distance_to_bolt tiger_acceleration bolt_speed = "Bolt" → tiger_time > bolt_time) ∧
    (race_winner finish distance_to_bolt tiger_acceleration bolt_speed = "Tiger" → tiger_time ≤ bolt_time) := sorry

theorem infinite_acceleration_tiger_wins (finish : Float) (distance_to_bolt : Float) (bolt_speed : Float)
    (h1 : finish > 0)
    (h2 : distance_to_bolt > 0)
    (h3 : bolt_speed > 0)
    (h4 : tiger_acceleration > 1000000) :
    race_winner finish distance_to_bolt tiger_acceleration bolt_speed = "Tiger" := sorry

/-
info: 'Bolt'
-/
-- #guard_msgs in
-- #eval race_winner 10 100 10 10

/-
info: 'Tiger'
-/
-- #guard_msgs in
-- #eval race_winner 100 10 5 10

/-
info: 'Tiger'
-/
-- #guard_msgs in
-- #eval race_winner 50 50 5 5
-- </vc-theorems>
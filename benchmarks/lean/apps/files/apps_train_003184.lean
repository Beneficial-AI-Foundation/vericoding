-- <vc-helpers>
-- </vc-helpers>

def evil_code_medal (user_time gold silver bronze : String) : String :=
sorry

theorem evil_code_medal_valid_output (user_time gold silver bronze : String) :
  let result := evil_code_medal user_time gold silver bronze
  result = "Gold" ∨ result = "Silver" ∨ result = "Bronze" ∨ result = "None" :=
sorry

theorem evil_code_medal_gold_condition (user_time gold silver bronze : String) :
  evil_code_medal user_time gold silver bronze = "Gold" →
  user_time < gold :=
sorry

theorem evil_code_medal_silver_condition (user_time gold silver bronze : String) :
  evil_code_medal user_time gold silver bronze = "Silver" →
  user_time ≥ gold ∧ user_time < silver :=
sorry

theorem evil_code_medal_bronze_condition (user_time gold silver bronze : String) :
  evil_code_medal user_time gold silver bronze = "Bronze" →
  user_time ≥ silver ∧ user_time < bronze :=
sorry

theorem evil_code_medal_none_condition (user_time gold silver bronze : String) :
  evil_code_medal user_time gold silver bronze = "None" →
  user_time ≥ bronze :=
sorry

theorem evil_code_medal_identical_times (t : String) :
  evil_code_medal t t t t = "None" :=
sorry

/-
info: 'Silver'
-/
-- #guard_msgs in
-- #eval evil_code_medal "00:30:00" "00:15:00" "00:45:00" "01:15:00"

/-
info: 'None'
-/
-- #guard_msgs in
-- #eval evil_code_medal "01:15:00" "00:15:00" "00:45:00" "01:15:00"

/-
info: 'Gold'
-/
-- #guard_msgs in
-- #eval evil_code_medal "00:00:01" "00:00:10" "00:01:40" "01:00:00"

-- Apps difficulty: introductory
-- Assurance level: unguarded
-- <vc-helpers>
-- </vc-helpers>

def hero (bullets : Int) (dragons : Int) : Bool := sorry

theorem hero_property {bullets dragons : Int} (hb : bullets ≥ 0) (hd : dragons ≥ 0) : 
  hero bullets dragons = (bullets ≥ dragons * 2) := sorry

theorem minimum_bullets_success {dragons : Int} (hd : dragons ≥ 0) :
  hero (dragons * 2) dragons = true := sorry

theorem minimum_bullets_failure {dragons : Int} (hd : dragons > 0) :
  hero (dragons * 2 - 1) dragons = false := sorry

theorem negative_bullets {bullets dragons : Int} (hb : bullets < 0) (hd : dragons ≥ 0) :
  hero bullets dragons = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval hero 10 5

/-
info: False
-/
-- #guard_msgs in
-- #eval hero 7 4

/-
info: False
-/
-- #guard_msgs in
-- #eval hero 4 5

-- Apps difficulty: introductory
-- Assurance level: unguarded
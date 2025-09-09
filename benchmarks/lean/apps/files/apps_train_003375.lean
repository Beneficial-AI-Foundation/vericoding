-- <vc-helpers>
-- </vc-helpers>

def chromosome_check (sperm : String) : String := sorry

theorem chromosome_check_XY :
  (chromosome_check "XY").contains 's' ∧ 
  (chromosome_check "XY").contains 'o' ∧ 
  (chromosome_check "XY").contains 'n' :=
sorry

theorem chromosome_check_XX :
  (chromosome_check "XX").contains 'd' ∧ 
  (chromosome_check "XX").contains 'a' ∧ 
  (chromosome_check "XX").contains 'u' ∧
  (chromosome_check "XX").contains 'g' ∧ 
  (chromosome_check "XX").contains 'h' ∧ 
  (chromosome_check "XX").contains 't' ∧
  (chromosome_check "XX").contains 'e' ∧ 
  (chromosome_check "XX").contains 'r' :=
sorry

/-
info: "Congratulations! You're going to have a son."
-/
-- #guard_msgs in
-- #eval chromosome_check "XY"

/-
info: "Congratulations! You're going to have a daughter."
-/
-- #guard_msgs in
-- #eval chromosome_check "XX"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
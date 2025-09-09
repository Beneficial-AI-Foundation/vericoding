-- <vc-helpers>
-- </vc-helpers>

def bonus_time (salary : Nat) (bonus : Bool) : String := sorry

theorem bonus_time_starts_with_dollar
  (salary : Nat) (bonus : Bool) :
  (bonus_time salary bonus).get! 0 = '$' := sorry

theorem bonus_time_value_correct
  (salary : Nat) (bonus : Bool) :
  let result := bonus_time salary bonus
  let value := String.toNat! (result.drop 1)
  value = if bonus then salary * 10 else salary := sorry

/-
info: '$100000'
-/
-- #guard_msgs in
-- #eval bonus_time 10000 True

/-
info: '$250000'
-/
-- #guard_msgs in
-- #eval bonus_time 25000 True

/-
info: '$10000'
-/
-- #guard_msgs in
-- #eval bonus_time 10000 False

-- Apps difficulty: introductory
-- Assurance level: unguarded
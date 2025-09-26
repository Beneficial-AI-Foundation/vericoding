-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_challenge (pledged current : Nat) (month : Month) : String := sorry

/- Completeness property -/
-- </vc-definitions>

-- <vc-theorems>
theorem check_challenge_completed 
  {pledged current : Nat} {month : Month}
  (h : pledged = current) : 
  check_challenge pledged current month = "Challenge is completed." := sorry

/- January always on track -/

theorem check_challenge_january
  {pledged current : Nat}
  (h : pledged ≠ current) :
  check_challenge pledged current Month.January = "You are on track." := sorry

/- Output format property -/

theorem check_challenge_format
  {pledged current : Nat} {month : Month} :
  (check_challenge pledged current month = "Challenge is completed." ∨
   check_challenge pledged current month = "You are on track." ∨
   ∃ n : Nat, check_challenge pledged current month = s!"{n} ahead of schedule!" ∨
             check_challenge pledged current month = s!"{n} behind schedule.") := sorry

/- Behind implies lower progress -/

theorem check_challenge_behind
  {pledged current : Nat} {month : Month} {n : Nat}
  (h : check_challenge pledged current month = s!"{n} behind schedule.") :
  n > 0 := sorry

/- Ahead implies higher progress -/

theorem check_challenge_ahead  
  {pledged current : Nat} {month : Month} {n : Nat}
  (h : check_challenge pledged current month = s!"{n} ahead of schedule!") :
  n > 0 := sorry

/- Zero current property -/

theorem check_challenge_zero
  {pledged : Nat} {month : Month} :
  check_challenge pledged 0 month = 
    if pledged = 0 then
      "Challenge is completed."
    else if month = Month.January then 
      "You are on track."
    else
      s!"{pledged} behind schedule." := sorry

/-
info: 'You are on track.'
-/
-- #guard_msgs in
-- #eval check_challenge 12 1 "February"

/-
info: 'You are 1 behind schedule.'
-/
-- #guard_msgs in
-- #eval check_challenge 12 1 "March"

/-
info: 'Challenge is completed.'
-/
-- #guard_msgs in
-- #eval check_challenge 12 12 "September"
-- </vc-theorems>
/-
Converting a normal (12-hour) time like "8:30 am" or "8:30 pm" to 24-hour time (like "0830" or "2030") sounds easy enough, right?  Well, let's see if you can do it!

You will have to define a function named "to24hourtime", and you will be given an hour (always in the range of 1 to 12, inclusive), a minute (always in the range of 0 to 59, inclusive), and a period (either "am" or "pm") as input.

Your task is to return a four-digit string that encodes that time in 24-hour time.
-/

-- <vc-helpers>
-- </vc-helpers>

def strToNat (s : String) : Nat := sorry

def to24hourtime (hour : Nat) (minute : Nat) (period : String) : String := sorry

theorem to24hourtime_format {hour : Nat} {minute : Nat} {period : String}
  (h1 : 1 ≤ hour ∧ hour ≤ 12) 
  (h2 : minute ≤ 59)
  (h3 : period = "am" ∨ period = "pm") :
  let result := to24hourtime hour minute period
  -- Result is 4 digits
  (result.length = 4) ∧ 
  -- Hours in bounds
  (strToNat (result.take 2) ≤ 23) ∧
  -- Minutes in bounds  
  (strToNat (result.drop 2) ≤ 59) ∧
  -- AM case
  ((period = "am" → 
    if hour = 12 
    then strToNat (result.take 2) = 0
    else strToNat (result.take 2) = hour) ∧
  -- PM case
   (period = "pm" →
    if hour = 12
    then strToNat (result.take 2) = 12 
    else strToNat (result.take 2) = hour + 12)) ∧
  -- Minutes preserved
  (strToNat (result.drop 2) = minute) := sorry

theorem am_pm_difference {hour : Nat} {minute : Nat}
  (h1 : 1 ≤ hour ∧ hour ≤ 12)
  (h2 : minute ≤ 59) :
  let am_time := strToNat (to24hourtime hour minute "am")
  let pm_time := strToNat (to24hourtime hour minute "pm")
  if hour = 12
  then pm_time - am_time = 1200
  else pm_time - am_time = 1200 ∨ am_time - pm_time = 1200 := sorry

/-
info: '0000'
-/
-- #guard_msgs in
-- #eval to24hourtime 12 0 "am"

/-
info: '0830'
-/
-- #guard_msgs in
-- #eval to24hourtime 8 30 "am"

/-
info: '2030'
-/
-- #guard_msgs in
-- #eval to24hourtime 8 30 "pm"

-- Apps difficulty: introductory
-- Assurance level: unguarded
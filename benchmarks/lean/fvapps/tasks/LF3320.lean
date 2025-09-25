-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def strToNat (s : String) : Nat := sorry

def to24hourtime (hour : Nat) (minute : Nat) (period : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>
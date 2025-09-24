-- <vc-preamble>
def subtractSeconds (date_str : String) (seconds : Nat) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def seconds_ago (date_str : String) (seconds : Nat) : String :=
  sorry

/- Theorems -/
-- </vc-definitions>

-- <vc-theorems>
theorem seconds_ago_subtracts_correctly (date_str : String) (seconds : Nat) 
  (h1 : seconds ≤ 86400) -- Max 1 day of seconds
  (h2 : IsValidDateTime date_str) :
  seconds_ago date_str seconds = 
    subtractSeconds date_str seconds
  := sorry

theorem seconds_ago_zero (date_str : String)
  (h : IsValidDateTime date_str) :
  seconds_ago date_str 0 = date_str
  := sorry

theorem seconds_ago_invalid_format (date_str : String)
  (h : ¬IsValidDateTime date_str) :
  IsError (seconds_ago date_str 1)
  := sorry

/-
info: '1999-12-31 23:59:59'
-/
-- #guard_msgs in
-- #eval seconds_ago "2000-01-01 00:00:00" 1

/-
info: '0001-02-03 04:04:59'
-/
-- #guard_msgs in
-- #eval seconds_ago "0001-02-03 04:05:06" 7
-- </vc-theorems>
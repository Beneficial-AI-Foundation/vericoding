-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def timeToWords (time: String) : String :=
sorry

def hasSubstring (s1 s2 : String) : Bool :=
sorry

def endsWithStr (s1 s2 : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem time_to_words_basic_format (hours : Nat) (minutes : Nat)
  (h_hours : hours ≤ 23) (h_minutes : minutes ≤ 59) :
  let result := timeToWords s!"#{hours}:#{minutes}"
  (hasSubstring result "o'clock" ∨ hasSubstring result "past" ∨
   hasSubstring result "to" ∨ result = "midnight") :=
sorry

theorem time_to_words_oclock (hours : Nat) (h_hours : hours ≤ 23) :
  let result := timeToWords s!"#{hours}:00"
  (hours = 0 → result = "midnight") ∧
  (hours ≠ 0 → endsWithStr result "o'clock") :=
sorry

theorem time_to_words_quarter_past (hours : Nat) (h_hours : hours ≤ 23) :
  let result := timeToWords s!"#{hours}:15"
  (hours = 0 → hasSubstring result "quarter past midnight") ∧
  (hours ≠ 0 → hasSubstring result "quarter past") :=
sorry

theorem time_to_words_half_past (hours : Nat) (h_hours : hours ≤ 23) :
  let result := timeToWords s!"#{hours}:30"
  (hours = 0 → hasSubstring result "half past midnight") ∧
  (hours ≠ 0 → hasSubstring result "half past") :=
sorry

theorem time_to_words_past_minutes (hours minutes : Nat)
  (h_hours : hours ≤ 23) (h_minutes : minutes ≤ 29) (h_minutes_pos : minutes ≥ 1)
  (h_not_quarter : minutes ≠ 15) :
  let result := timeToWords s!"#{hours}:#{minutes}"
  hasSubstring result "past" ∧ hasSubstring result "minute" ∧
  (hasSubstring result "minutes" ↔ minutes ≠ 1) :=
sorry

theorem time_to_words_to_minutes (hours minutes : Nat)
  (h_hours : hours ≤ 23) (h_minutes : minutes ≤ 59) (h_minutes_low : minutes ≥ 31)
  (h_not_quarter : minutes ≠ 45) :
  let result := timeToWords s!"#{hours}:#{minutes}"
  hasSubstring result "to" ∧ hasSubstring result "minute" :=
sorry
-- </vc-theorems>
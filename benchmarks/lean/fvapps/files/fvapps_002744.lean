-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_pretty (seconds : Nat) : String := sorry

theorem to_pretty_format (seconds : Nat) (h : seconds ≤ 1000000) : 
  (to_pretty seconds).endsWith " ago" ∨ to_pretty seconds = "just now" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem to_pretty_words (seconds : Nat) (h : seconds ≤ 1000000) :
  let words := (to_pretty seconds).split fun c => c = ' '
  words.head! = "just" ∨ 
  words.head!.all Char.isDigit ∨
  words.head! = "a" ∨ 
  words.head! = "an" := sorry

theorem zero_is_just_now : 
  to_pretty 0 = "just now" := sorry

theorem single_second :
  to_pretty 1 = "a second ago" := sorry

theorem multiple_seconds (seconds : Nat) (h1 : seconds > 1) (h2 : seconds ≤ 59) :
  to_pretty seconds = s!"{seconds} seconds ago" := sorry

theorem single_minute (seconds : Nat) (h1 : seconds ≥ 61) (h2 : seconds < 120) :
  to_pretty seconds = "a minute ago" := sorry

theorem multiple_minutes (seconds : Nat) (h1 : seconds ≥ 120) (h2 : seconds ≤ 3599) :
  to_pretty seconds = s!"{seconds / 60} minutes ago" := sorry

theorem single_hour (seconds : Nat) (h1 : seconds ≥ 3601) (h2 : seconds < 7200) :
  to_pretty seconds = "an hour ago" := sorry

theorem multiple_hours (seconds : Nat) (h1 : seconds ≥ 7200) (h2 : seconds ≤ 86399) :
  to_pretty seconds = s!"{seconds / 3600} hours ago" := sorry
-- </vc-theorems>
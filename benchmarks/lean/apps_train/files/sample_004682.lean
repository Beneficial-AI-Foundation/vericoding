/-
Polly is 8 years old. She is eagerly awaiting Christmas as she has a bone to pick with Santa Claus. Last year she asked for a horse, and he brought her a dolls house. Understandably she is livid.

The days seem to drag and drag so Polly asks her friend to help her keep count of how long it is until Christmas, in days. She will start counting from the first of December.

Your function should take 1 argument (a Date object) which will be the day of the year it is currently. The function should then work out how many days it is until Christmas.

Watch out for leap years!
-/

def isLeapYear (year : Int) : Bool := sorry

def daysUntilChristmas (d : Date) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def addDays (d : Date) (n : Nat) : Date := sorry

theorem days_until_christmas_non_negative (d : Date) : 
  daysUntilChristmas d ≥ 0 := sorry

theorem days_until_christmas_max_bound (d : Date) :
  daysUntilChristmas d ≤ 366 := sorry

theorem days_until_christmas_gives_christmas (d : Date) :
  let future := addDays d (daysUntilChristmas d)
  future.month = 12 ∧ future.day = 25 := sorry

theorem on_christmas_returns_zero (d : Date) (h1 : d.month = 12) (h2 : d.day = 25) :
  daysUntilChristmas d = 0 := sorry

theorem after_christmas_next_year (d : Date) 
  (h1 : d.month = 12) (h2 : d.day > 25) :
  daysUntilChristmas d = 
    daysUntilChristmas (Date.mk (d.year + 1) 12 25) := sorry

/-
info: 163
-/
-- #guard_msgs in
-- #eval days_until_christmas date(2023, 7, 15)

/-
info: 365
-/
-- #guard_msgs in
-- #eval days_until_christmas date(2023, 12, 26)

/-
info: 1
-/
-- #guard_msgs in
-- #eval days_until_christmas date(2023, 12, 24)

-- Apps difficulty: introductory
-- Assurance level: unguarded
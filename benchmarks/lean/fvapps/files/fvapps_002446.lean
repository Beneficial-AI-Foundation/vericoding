-- <vc-preamble>
def get_weekday_name (month : Nat) (day : Nat) (year : Nat) : String := sorry

structure Date where
  month : Nat
  day : Nat 
  year : Nat

def IsValidDate (d : Date) : Prop := sorry
def weekday (d : Date) : Nat := sorry

def calendar_day_name (n : Nat) : String := sorry
def IsUppercase (s : String) : Prop := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsValidWeekdayName (s : String) : Prop := sorry

theorem get_weekday_name_matches_calendar
    (m : Nat) (d : Nat) (y : Nat)
    (h1 : 1 ≤ m ∧ m ≤ 12)
    (h2 : 1 ≤ d ∧ d ≤ 31)
    (h3 : 1900 ≤ y ∧ y ≤ 2100)
    (h4 : IsValidDate ⟨m, d, y⟩) : 
    get_weekday_name m d y = calendar_day_name (weekday ⟨m, d, y⟩) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_weekday_name_returns_uppercase
    (m : Nat) (d : Nat) (y : Nat)
    (h1 : 1 ≤ m ∧ m ≤ 12) 
    (h2 : 1 ≤ d ∧ d ≤ 31)
    (h3 : 1900 ≤ y ∧ y ≤ 2100) :
    IsValidDate ⟨m, d, y⟩ →
    (IsUppercase (get_weekday_name m d y) ∧ 
     IsValidWeekdayName (get_weekday_name m d y)) := sorry

/-
info: 'WEDNESDAY'
-/
-- #guard_msgs in
-- #eval get_weekday_name 8 5 2015

/-
info: 'SUNDAY'
-/
-- #guard_msgs in
-- #eval get_weekday_name 1 1 2023

/-
info: 'MONDAY'
-/
-- #guard_msgs in
-- #eval get_weekday_name 12 25 2023
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
-- <vc-preamble>
structure Date where
  month : Nat
  day : Nat
  year : Nat
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_weekday_name (month : Nat) (day : Nat) (year : Nat) : String :=
sorry

def IsValidDate (d : Date) : Prop :=
sorry

def weekday (d : Date) : Nat :=
sorry

def calendar_day_name (n : Nat) : String :=
sorry

def IsUppercase (s : String) : Prop :=
sorry

def IsValidWeekdayName (s : String) : Prop :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_weekday_name_matches_calendar
    (m : Nat) (d : Nat) (y : Nat)
    (h1 : 1 ≤ m ∧ m ≤ 12)
    (h2 : 1 ≤ d ∧ d ≤ 31)
    (h3 : 1900 ≤ y ∧ y ≤ 2100)
    (h4 : IsValidDate ⟨m, d, y⟩) :
    get_weekday_name m d y = calendar_day_name (weekday ⟨m, d, y⟩) :=
sorry

theorem get_weekday_name_returns_uppercase
    (m : Nat) (d : Nat) (y : Nat)
    (h1 : 1 ≤ m ∧ m ≤ 12)
    (h2 : 1 ≤ d ∧ d ≤ 31)
    (h3 : 1900 ≤ y ∧ y ≤ 2100) :
    IsValidDate ⟨m, d, y⟩ →
    (IsUppercase (get_weekday_name m d y) ∧
     IsValidWeekdayName (get_weekday_name m d y)) :=
sorry
-- </vc-theorems>
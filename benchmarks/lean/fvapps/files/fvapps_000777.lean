-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def DAYS : List String := ["saturday", "sunday", "monday", "tuesday", "wednesday", "thursday", "friday"]

def indexOfDay (day: String) : Nat :=
sorry

def solveCompetitionDuration (startDay endDay: String) (l r: Nat) : String ⊕ Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem competition_duration_impossible {startDay endDay: String} {l r: Nat}
  (h1: l ≤ r)
  (h2: solveCompetitionDuration startDay endDay l r = Sum.inl "impossible") :
  ∀ x, l ≤ x → x ≤ r →
    x % 7 ≠ ((indexOfDay endDay - indexOfDay startDay + 8) % 7) :=
sorry

theorem competition_duration_many {startDay endDay: String} {l r: Nat}
  (h1: l ≤ r)
  (h2: solveCompetitionDuration startDay endDay l r = Sum.inl "many") :
  ∃ x y, l ≤ x ∧ x < y ∧ y ≤ r ∧
    x % 7 = ((indexOfDay endDay - indexOfDay startDay + 8) % 7) ∧
    y % 7 = ((indexOfDay endDay - indexOfDay startDay + 8) % 7) :=
sorry

theorem competition_duration_specific {startDay endDay: String} {l r n: Nat}
  (h1: l ≤ r)
  (h2: solveCompetitionDuration startDay endDay l r = Sum.inr n) :
  l ≤ n ∧ n ≤ r ∧
  n % 7 = ((indexOfDay endDay - indexOfDay startDay + 8) % 7) ∧
  (∀ x, l ≤ x → x < n → x % 7 ≠ n % 7) ∧
  n + 7 > r :=
sorry

theorem same_day_property {day: String}
  (h: day ∈ DAYS) :
  solveCompetitionDuration day day 1 20 = Sum.inr 7 ∨
  solveCompetitionDuration day day 1 20 = Sum.inl "many" :=
sorry
-- </vc-theorems>
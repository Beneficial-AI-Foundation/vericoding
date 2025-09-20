-- <vc-preamble>
def dateCompare (d1 m1 y1 d2 m2 y2 : Int) : Bool :=
  if y1 ≠ y2 then y1 > y2
  else if m1 ≠ m2 then m1 > m2
  else d1 > d2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def days_until (date month year : Int) : Int :=
  sorry

def isValidDate (date month year : Int) : Bool :=
  sorry

def dateDiffDays (d1 m1 y1 d2 m2 y2 : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem days_until_is_int {date month year : Int}
  (h : isValidDate date month year = true) :
  ∃ n : Int, days_until date month year = n :=
sorry

theorem days_until_target_date {date month year : Int}
  (h1 : date = 24)
  (h2 : month = 3)
  (h3 : year = 2437) :
  days_until date month year = 0 :=
sorry

theorem days_until_future_dates {date month year : Int}
  (h1 : isValidDate date month year = true)
  (h2 : dateCompare date month year 24 3 2437 = true) :
  days_until date month year < 0 :=
sorry

theorem days_until_past_dates {date month year : Int}
  (h1 : isValidDate date month year = true)
  (h2 : dateCompare 24 3 2437 date month year = true) :
  days_until date month year > 0 :=
sorry

theorem days_until_symmetry {date month year : Int}
  (h : isValidDate date month year = true) :
  days_until date month year = dateDiffDays year month date 2437 3 24 :=
sorry
-- </vc-theorems>
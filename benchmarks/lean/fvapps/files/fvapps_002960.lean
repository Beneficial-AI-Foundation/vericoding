-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def yearDays (year : Int) : String := sorry

def isLeapYear (year : Int) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem yearDays_format {year : Int} : 
  yearDays year = s!"{year} has {if isLeapYear year then 366 else 365} days" := sorry

theorem yearDays_values {year : Int} :
  yearDays year = s!"{year} has 365 days" ∨ yearDays year = s!"{year} has 366 days" := sorry

theorem divisible_by_400_is_leap {year : Int} (h : year % 400 = 0) :
  yearDays year = s!"{year} has 366 days" := sorry

theorem divisible_by_4_not_100_is_leap {year : Int} (h1 : year % 4 = 0) (h2 : year % 100 ≠ 0) :
  yearDays year = s!"{year} has 366 days" := sorry
-- </vc-theorems>
-- <vc-preamble>
def Elements := ["Wood", "Fire", "Earth", "Metal", "Water"]

def Animals := ["Rat", "Ox", "Tiger", "Rabbit", "Dragon", "Snake",
               "Horse", "Goat", "Monkey", "Rooster", "Dog", "Pig"]

def String.splitToList (s : String) : List String :=
  s.split (· = ' ')
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chinese_zodiac (year : Int) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cycle_12_years {y : Int} (h : y ≥ 1900 ∧ y ≤ 2100) :
  (chinese_zodiac y).splitToList[1]! = (chinese_zodiac (y + 12)).splitToList[1]! :=
sorry

theorem cycle_10_years {y : Int} (h : y ≥ 1900 ∧ y ≤ 2100) :
  (chinese_zodiac y).splitToList[0]! = (chinese_zodiac (y + 10)).splitToList[0]! :=
sorry

theorem valid_format {year : Int} (h : year ≥ 1900 ∧ year ≤ 2100) :
  let result := chinese_zodiac year
  let parts := result.splitToList
  parts[0]! ∈ Elements ∧ parts[1]! ∈ Animals :=
sorry

theorem deterministic {year : Int} (h : year ≥ 1900 ∧ year ≤ 2100) :
  chinese_zodiac year = chinese_zodiac year :=
sorry
-- </vc-theorems>
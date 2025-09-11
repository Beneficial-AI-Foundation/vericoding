-- <vc-preamble>
def REQUIRED_STATIONS : List String := 
  ["Rejection", "Disappointment", "Backstabbing Central", "Shattered Dreams Parkway"]
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSubset (l1 l2 : List String) : Bool := sorry

def alan (stations : List String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem alan_complete {stations : List String} : 
  isSubset REQUIRED_STATIONS stations → 
  alan stations = "Smell my cheese you mother!" := sorry

theorem alan_incomplete {stations : List String} :
  ¬isSubset REQUIRED_STATIONS stations →
  alan stations = "No, seriously, run. You will miss it." := sorry

theorem alan_with_additional 
  {additional : List String} (h : additional.length ≥ 4) :
  alan (REQUIRED_STATIONS ++ additional) = "Smell my cheese you mother!" := sorry

theorem alan_with_incomplete_subset
  {subset : List String} (h : subset.length ≤ 3) 
  (h2 : ∀ x ∈ subset, x ∈ REQUIRED_STATIONS) :
  alan subset = "No, seriously, run. You will miss it." := sorry

/-
info: 'Smell my cheese you mother!'
-/
-- #guard_msgs in
-- #eval alan ["Norwich", "Rejection", "Disappointment", "Backstabbing Central", "Shattered Dreams Parkway", "London"]

/-
info: 'No, seriously, run. You will miss it.'
-/
-- #guard_msgs in
-- #eval alan ["London", "Norwich"]

/-
info: 'Smell my cheese you mother!'
-/
-- #guard_msgs in
-- #eval alan ["Norwich", "Rejection", "Disappointment", "Backstabbing Central", "Shattered Dreams Parkway"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def VALID_FIGHTERS := ["george saint pierre", "conor mcgregor"]

def quote (fighter : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem quote_case_insensitive (fighter : String)
  (h : fighter.toLower ∈ VALID_FIGHTERS) :
  ∀ casing, quote casing = quote fighter →
  casing.toLower = fighter.toLower :=
sorry

theorem quote_invalid_fighter (fighter : String) :
  fighter.toLower ∉ VALID_FIGHTERS → 
  ∀ result, ¬(quote fighter = result) :=
sorry

theorem non_matching_fighter_raises (invalid_name : String) :
  invalid_name.toLower ∉ VALID_FIGHTERS →
  ∀ result, ¬(quote invalid_name = result) := 
sorry

/-
info: 'I am not impressed by your performance.'
-/
-- #guard_msgs in
-- #eval quote "George Saint Pierre"

/-
info: "I'd like to take this chance to apologize.. To absolutely NOBODY!"
-/
-- #guard_msgs in
-- #eval quote "Conor McGregor"

/-
info: 'I am not impressed by your performance.'
-/
-- #guard_msgs in
-- #eval quote "george saint pierre"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
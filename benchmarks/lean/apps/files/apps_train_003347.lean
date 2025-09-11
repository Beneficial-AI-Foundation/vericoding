-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def quotable (name : String) (quote : String) : String := sorry

/- Property: Output contains both inputs and format is consistent -/
-- </vc-definitions>

-- <vc-theorems>
theorem quotable_format (name quote : String)
  (h1 : ¬ String.contains name '"')
  (h2 : ¬ String.contains quote '"') :
  (quotable name quote).startsWith name ∧ 
  (quotable name quote).endsWith ('"'.toString ++ quote ++ '"'.toString) ∧
  String.contains (quotable name quote) ' ' := sorry

/- Property: Quotes appear in correct places only -/

theorem quotable_quotes_placement (name quote : String)
  (h1 : ¬ String.contains name '"')
  (h2 : ¬ String.contains quote '"') :
  ((quotable name quote).data.filter (· = '"')).length = 2 := sorry

/- Property: Function is deterministic -/

theorem quotable_deterministic (name quote : String) :
  quotable name quote = quotable name quote := sorry

/-
info: 'Grae said: "Practice makes perfect"'
-/
-- #guard_msgs in
-- #eval quotable "Grae" "Practice makes perfect"

/-
info: 'Alex said: "Python is great fun"'
-/
-- #guard_msgs in
-- #eval quotable "Alex" "Python is great fun"

/-
info: 'Bethany said: "Yes, way more fun than R"'
-/
-- #guard_msgs in
-- #eval quotable "Bethany" "Yes, way more fun than R"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
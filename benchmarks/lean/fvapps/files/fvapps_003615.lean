-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def knight_or_knave (s : String) : String := sorry

theorem knight_or_knave_numeric_comparison (a b : Int) :
  let expr := toString a ++ "==" ++ toString b
  let result := knight_or_knave expr
  (result = "Knight!" ∨ result = "Knave! Do not trust.") ∧
  (result = "Knight!" ↔ a = b) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem knight_or_knave_boolean (b : Bool) :
  let expr := toString b
  knight_or_knave expr = (if b then "Knight!" else "Knave! Do not trust.") := sorry

theorem knight_or_knave_arithmetic (a b : Int) :
  let expr := toString a ++ "+" ++ toString b ++ "==" ++ toString (a + b)
  knight_or_knave expr = "Knight!" := sorry
-- </vc-theorems>
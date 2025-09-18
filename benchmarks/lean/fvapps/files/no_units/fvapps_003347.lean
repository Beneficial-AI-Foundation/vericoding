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
-- </vc-theorems>
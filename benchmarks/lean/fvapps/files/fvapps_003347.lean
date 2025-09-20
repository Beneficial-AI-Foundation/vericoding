-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def quotable (name : String) (quote : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem quotable_format (name quote : String)
  (h1 : ¬ String.contains name '"')
  (h2 : ¬ String.contains quote '"') :
  (quotable name quote).startsWith name ∧
  (quotable name quote).endsWith ('"'.toString ++ quote ++ '"'.toString) ∧
  String.contains (quotable name quote) ' ' :=
sorry

theorem quotable_quotes_placement (name quote : String)
  (h1 : ¬ String.contains name '"')
  (h2 : ¬ String.contains quote '"') :
  ((quotable name quote).data.filter (· = '"')).length = 2 :=
sorry

theorem quotable_deterministic (name quote : String) :
  quotable name quote = quotable name quote :=
sorry
-- </vc-theorems>
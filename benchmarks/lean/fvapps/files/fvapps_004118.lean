-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_match (s : String) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_match_empty (s : String) :
  s = "" → max_match s = [] :=
sorry

theorem max_match_happy_path1 (s : String) :
  s = "happyday" → max_match s = ["happy", "day"] :=
sorry

theorem max_match_happy_path2 (s : String) :
  s = "thecatsat" → max_match s = ["the", "cat", "sat"] :=
sorry

theorem max_match_edge_case (s : String) :
  s = "onthemat" → max_match s = ["on", "the", "mat"] :=
sorry
-- </vc-theorems>
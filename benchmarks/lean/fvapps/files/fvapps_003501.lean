-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.toList (xs : List α) : List α := xs

def table_game (table: List (List Int)) : List Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_value_property (x : Int) :
  let table := [[x, x + x, x], [x + x, x + x + x + x, x + x], [x, x + x, x]]
  table_game table = [x, x, x, x] := sorry

theorem valid_table_property (a b c d : Int) :
  let table := [[a, a + b, b], [a + c, a + b + c + d, b + d], [c, c + d, d]]
  table_game table = [a, b, c, d] := sorry
-- </vc-theorems>
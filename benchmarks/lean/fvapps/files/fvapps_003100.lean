-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_poker (john: String) (uncle: String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_poker_idempotent 
  (john: String) (uncle: String) :
  uncle = "S2D2H2C2" →
  sort_poker (sort_poker john uncle) uncle = sort_poker john uncle :=
sorry
-- </vc-theorems>
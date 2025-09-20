-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_change (money : Int) (coins : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_change_no_coins (money : Int) :
  count_change money [] = (if money = 0 then 1 else 0) :=
sorry
-- </vc-theorems>
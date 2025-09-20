-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cake (candles: Nat) (s: String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cake_empty_string :
  cake 10 "" = "That was close!" :=
sorry

theorem cake_zero_candles :
  cake 0 "abc" = "That was close!" :=
sorry 

theorem cake_known_case1 :
  cake 900 "abcdef" = "That was close!" :=
sorry

theorem cake_known_case2 :
  cake 56 "ifkhchlhfd" = "Fire!" := 
sorry
-- </vc-theorems>
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def scramble_message (step : Nat) (input : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem scramble_message_fixed_chef :
  scramble_message 2 "chef" = "cehf" :=
sorry

theorem scramble_message_fixed_pie :
  scramble_message 4 "enjoyourapplepie" = "eayejpuinpopolre" := 
sorry

theorem scramble_message_fixed_abcd :
  scramble_message 2 "abcd" = "acbd" :=
sorry 

theorem scramble_message_fixed_abcdefgh :
  scramble_message 3 "abcdefgh" = "aecgbfdh" :=
sorry
-- </vc-theorems>
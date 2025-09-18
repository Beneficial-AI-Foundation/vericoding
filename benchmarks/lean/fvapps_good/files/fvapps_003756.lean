-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def custom_fib (signature : List Int) (indexes : List Int) (n : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem known_sequence_1 :
  custom_fib [1,1] [0,1] 3 = 3 :=
sorry

theorem known_sequence_2 :
  custom_fib [0,1] [0,1] 5 = 5 :=
sorry

theorem known_sequence_3 :
  custom_fib [1,2,3] [0,1,2] 3 = 6 :=
sorry
-- </vc-theorems>
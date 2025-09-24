-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def alex_mistakes (num_kata : Nat) (total_time : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem alex_mistakes_nonnegative
  (num_kata : Nat) (total_time : Nat) :
  alex_mistakes num_kata total_time ≥ 0 :=
sorry

theorem alex_mistakes_time_limit
  (num_kata total_time : Nat)
  (h1 : total_time > num_kata * 6) :
  let result := alex_mistakes num_kata total_time
  let remaining_time := total_time - num_kata * 6
  let mistake_time := (2^result - 1) * 5
  mistake_time ≤ remaining_time ∧
  ((2^(result+1) - 1) * 5 > remaining_time ∨ result ≥ 32) :=
sorry

theorem alex_mistakes_no_extra_time 
  (num_kata : Nat)
  (h1 : num_kata > 0) :
  alex_mistakes num_kata (num_kata * 6) = 0 ∧
  alex_mistakes num_kata (num_kata * 6 - 1) = 0 :=
sorry

theorem alex_mistakes_monotonic
  (num_kata : Nat)
  (extra_time : Nat)
  (h1 : extra_time > 0) :
  alex_mistakes num_kata (num_kata * 6 + extra_time + 1) ≥ 
  alex_mistakes num_kata (num_kata * 6 + extra_time) :=
sorry
-- </vc-theorems>
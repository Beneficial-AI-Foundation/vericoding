-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def kooka_counter (s: String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem kooka_counter_nonnegative (s: String) : 
  kooka_counter s ≥ 0 := 
sorry

theorem kooka_counter_empty : 
  kooka_counter "" = 0 := 
sorry

theorem kooka_counter_consecutive_laughs (n: Nat) (h: n > 0) :
  kooka_counter (String.join (List.replicate n "ha")) = 1 ∧ 
  kooka_counter (String.join (List.replicate n "Ha")) = 1 :=
sorry

theorem kooka_counter_alternating_laughs (n: Nat) (h: n > 0) :
  let lowerLaugh := String.join (List.replicate n "ha")
  let upperLaugh := String.join (List.replicate n "Ha")
  kooka_counter (lowerLaugh ++ upperLaugh) = 2 :=
sorry
-- </vc-theorems>
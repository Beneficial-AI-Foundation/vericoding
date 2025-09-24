-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortest_steps_to_num (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem steps_always_positive (n : Nat) (h : n > 0) : 
  shortest_steps_to_num n ≥ 0 :=
sorry

theorem reaches_one (n : Nat) (h : n > 0) :
  let steps := shortest_steps_to_num n
  let result := (n : Nat)
  let final := Nat.recOn steps result (λ _ acc => 
    if acc % 2 = 0 
    then acc / 2
    else acc - 1)
  final = 1 :=
sorry

theorem powers_of_two (n : Nat) (h : n > 0) :
  shortest_steps_to_num (2^n) = n :=
sorry
-- </vc-theorems>
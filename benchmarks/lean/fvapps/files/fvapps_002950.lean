-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reindeer (presents : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reindeer_min_two (presents : Nat) (h : presents ≤ 180) : 
  reindeer presents ≥ 2 := 
  sorry

theorem reindeer_formula (presents : Nat) (h : presents ≤ 180) :
  reindeer presents = (presents + 29) / 30 + 2 :=
  sorry

theorem reindeer_invalid_input (presents : Nat) (h : presents > 180) :
  reindeer presents = 0 :=
  sorry

theorem reindeer_is_nat (presents : Nat) (h : presents ≤ 180) :
  ∃ n : Nat, reindeer presents = n :=
  sorry

theorem reindeer_max_eight (presents : Nat) (h : presents ≤ 180) :
  reindeer presents ≤ 8 :=
  sorry
-- </vc-theorems>
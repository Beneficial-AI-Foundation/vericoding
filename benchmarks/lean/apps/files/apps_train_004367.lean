-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def animals (heads legs : Int) : Option (Int × Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_combinations
  (chickens cows : Int)
  (h_chickens : chickens ≥ 0)
  (h_cows : cows ≥ 0)
  (h_chickens_bound : chickens ≤ 1000)
  (h_cows_bound : cows ≤ 1000) :
  animals (chickens + cows) (2*chickens + 4*cows) = some (chickens, cows) :=
sorry

theorem invalid_combinations
  (heads legs : Int)
  (h_invalid : ¬(heads ≥ 0 ∧ legs ≥ 0 ∧ legs % 2 = 0 ∧
               (let possible_chickens := 2*heads - legs/2
                let possible_cows := legs/2 - heads
                possible_chickens ≥ 0 ∧ possible_cows ≥ 0))) :
  animals heads legs = none :=
sorry

theorem zero_case :
  animals 0 0 = some (0, 0) :=
sorry

theorem impossible_leg_counts
  (heads : Int)
  (h_heads_pos : heads > 0)
  (h_heads_bound : heads ≤ 1000) : 
  animals heads (2*heads - 1) = none :=
sorry

/-
info: (44, 28)
-/
-- #guard_msgs in
-- #eval animals 72 200

/-
info: (0, 0)
-/
-- #guard_msgs in
-- #eval animals 0 0

/-
info: 'No solutions'
-/
-- #guard_msgs in
-- #eval animals 25 555
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
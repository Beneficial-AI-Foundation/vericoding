-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def classify_distributions (villages : List (List Nat)) : List ClassificationType :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem classify_distributions_output_length {villages : List (List Nat)} :
  (villages.all (fun v => v.length > 0)) →
  (villages.all (fun v => v.all (fun x => x > 0))) →
  (classify_distributions villages).length = villages.length :=
sorry

theorem classify_distributions_valid_values {villages : List (List Nat)} :
  (villages.all (fun v => v.length > 0)) →
  (villages.all (fun v => v.all (fun x => x > 0))) →
  (classify_distributions villages).all (fun r => r == ClassificationType.uniform || r == ClassificationType.poisson) :=
sorry

theorem classify_distributions_input_constraints {villages : List (List Nat)} :
  villages.all (fun v => v.length > 0) →
  villages.all (fun v => v.all (fun x => x > 0)) →
  villages.all (fun v => v.length ≥ 5 ∧ v.length ≤ 50) →
  classify_distributions villages ≠ [] :=
sorry

/-
info: ['poisson']
-/
-- #guard_msgs in
-- #eval classify_distributions [[92, 100, 99, 109, 93, 105, 103, 106, 101, 99] * 25]

/-
info: ['uniform']
-/
-- #guard_msgs in
-- #eval classify_distributions [[28, 180, 147, 53, 84, 80, 180, 85, 8, 16] * 25]

/-
info: ['poisson', 'uniform']
-/
-- #guard_msgs in
-- #eval classify_distributions [[92, 100, 99, 109, 93, 105, 103, 106, 101, 99] * 25, [28, 180, 147, 53, 84, 80, 180, 85, 8, 16] * 25]
-- </vc-theorems>
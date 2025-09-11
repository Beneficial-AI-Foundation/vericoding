-- <vc-preamble>
def isPrime (n : Nat) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def goldbach (n : Nat) : List (List Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem goldbach_valid_sums {n : Nat} (h : n ≥ 4) (h2 : n % 2 = 0) :
  let result := goldbach n
  (∀ x ∈ result, x.length = 2) ∧ 
  (∀ x ∈ result, x[0]! + x[1]! = n) ∧
  (∀ x ∈ result, x[0]! ≤ x[1]!) :=
sorry

theorem goldbach_small_inputs {n : Nat} (h : n ≤ 3) :
  goldbach n = [] :=
sorry

theorem goldbach_four :
  goldbach 4 = [[2, 2]] :=
sorry

/-
info: [[3, 7], [5, 5]]
-/
-- #guard_msgs in
-- #eval goldbach 10

/-
info: [[5, 47], [11, 41], [23, 29]]
-/
-- #guard_msgs in
-- #eval goldbach 52

/-
info: [[5, 53], [11, 47], [17, 41], [29, 29]]
-/
-- #guard_msgs in
-- #eval goldbach 58
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
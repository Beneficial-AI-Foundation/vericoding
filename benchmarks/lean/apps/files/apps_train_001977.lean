-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_minimum_distance (n : Nat) (positions : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_n_result {n : Nat} (h : n ≥ 2) (h2 : n % 2 = 0) 
  (positions : List Nat) (h3 : positions.length = n) :
  (find_minimum_distance n positions) ≥ 0 :=
sorry

theorem sorted_positions_same_result {n : Nat} (h : n ≥ 2) (h2 : n % 2 = 0)
  (positions1 positions2 : List Nat) 
  (h3 : positions1.length = n)
  (h4 : positions2.length = n)
  (h5 : ∀ x, x ∈ positions1 ↔ x ∈ positions2) :
  find_minimum_distance n positions1 = find_minimum_distance n positions2 :=
sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval find_minimum_distance 6 [0, 1, 3, 7, 15, 31]

/-
info: 36
-/
-- #guard_msgs in
-- #eval find_minimum_distance 2 [73, 37]

/-
info: 500000000
-/
-- #guard_msgs in
-- #eval find_minimum_distance 4 [0, 500000000, 500000001, 1000000000]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded
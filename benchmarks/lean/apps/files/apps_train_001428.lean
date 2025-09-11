-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_nearest_cabs (n m : Nat) (cabs : List (List Int)) (trips : List (List Int)) : List Nat :=
  sorry

-- Result length matches number of trips
-- </vc-definitions>

-- <vc-theorems>
theorem find_nearest_cabs_length {n m : Nat} {cabs : List (List Int)} {trips : List (List Int)} :
  (∀ c ∈ cabs, List.length c = 2) →
  (∀ t ∈ trips, List.length t = 4) →
  List.length (find_nearest_cabs n m cabs trips) = m :=
sorry

-- Result values are valid cab indices

theorem find_nearest_cabs_valid_indices {n m : Nat} {cabs : List (List Int)} {trips : List (List Int)} : 
  (∀ r ∈ find_nearest_cabs n m cabs trips, 1 ≤ r ∧ r ≤ n) :=
sorry

-- First available cab is chosen when all cabs are equidistant

theorem find_nearest_cabs_equidistant {n m : Nat} {trips : List (List Int)} :
  let cabs := List.replicate n [0, 0]
  let result := find_nearest_cabs n m cabs trips
  trips ≠ [] →
  List.head! result = 1 :=
sorry

/-
info: [1, 1]
-/
-- #guard_msgs in
-- #eval find_nearest_cabs 3 2 [[1, 3], [3, 2], [3, 5]] [[2, 3, 3, 4], [5, 3, 4, 1]]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval find_nearest_cabs 1 1 [[0, 0]] [[1, 1, 2, 2]]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval find_nearest_cabs 2 1 [[1, 1], [1, 1]] [[2, 2, 3, 3]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def asteroidCollision (asteroids : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_valid_asteroid_list
  (asteroids : List Int) :
  let result := asteroidCollision asteroids
  ∀ x ∈ result, x ≠ 0 :=
sorry

theorem empty_and_single_preserved
  (asteroids : List Int) :
  List.length asteroids ≤ 1 →
  asteroidCollision asteroids = asteroids :=
sorry

theorem all_negative_preserved
  (asteroids : List Int) :
  let negative_asteroids := asteroids.map (fun x => -(x.natAbs))
  let result := asteroidCollision negative_asteroids
  (∀ x ∈ result, x < 0) ∧
  (result.length = negative_asteroids.length) :=
sorry

theorem all_positive_preserved
  (asteroids : List Int) :
  let positive_asteroids := asteroids.map (fun x => x.natAbs)
  let result := asteroidCollision positive_asteroids
  (∀ x ∈ result, x > 0) ∧
  (result.length = positive_asteroids.length) :=
sorry

theorem equal_size_opposite_direction_collision
  (asteroids : List Int)
  (h : asteroids.length ≥ 2)
  (size : Int) :
  asteroidCollision [size, -size] = [] :=
sorry
-- </vc-theorems>
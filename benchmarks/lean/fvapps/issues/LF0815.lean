-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def best_movie (lengths ratings : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem best_movie_result_in_bounds {lengths ratings : List Nat} 
  (h1 : lengths.length = ratings.length)
  (h2 : lengths.length > 0) :
  1 ≤ best_movie lengths ratings ∧ best_movie lengths ratings ≤ lengths.length :=
sorry

theorem best_movie_maximizes_product {lengths ratings : List Nat}
  (h1 : lengths.length = ratings.length)
  (h2 : lengths.length > 0) :
  let result := best_movie lengths ratings - 1
  let max_prod := lengths[result]! * ratings[result]!
  ∀ i, i < lengths.length →
    lengths[i]! * ratings[i]! ≤ max_prod :=
sorry

theorem best_movie_highest_rating_on_equal_product {lengths ratings : List Nat}
  (h1 : lengths.length = ratings.length)
  (h2 : lengths.length > 0) :
  let result := best_movie lengths ratings - 1
  let max_prod := lengths[result]! * ratings[result]!
  ∀ i, i < lengths.length →
    lengths[i]! * ratings[i]! = max_prod →
    ratings[i]! ≤ ratings[result]! :=
sorry

theorem best_movie_identical_ratings {lengths : List Nat} 
  (h : lengths.length > 0)
  (hmax : (List.maximum? lengths).isSome) :
  let ratings := List.replicate lengths.length 1
  let result := best_movie lengths ratings - 1
  lengths[result]! = (List.maximum? lengths).get hmax :=
sorry

theorem best_movie_identical_lengths {ratings : List Nat}
  (h : ratings.length > 0)
  (hmax : (List.maximum? ratings).isSome) :
  let lengths := List.replicate ratings.length 1
  let result := best_movie lengths ratings - 1
  ratings[result]! = (List.maximum? ratings).get hmax :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval best_movie [1, 2] [2, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval best_movie [2, 1, 4, 1] [2, 4, 1, 4]
-- </vc-theorems>
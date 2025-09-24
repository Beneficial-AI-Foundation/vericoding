-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Int) : Int := sorry

def check_sqrt_accuracy (scale tolerance : Int) (numbers : List Int) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_preservation {scale tolerance : Int} {numbers : List Int}
  (h1 : 0 < tolerance) (h2 : tolerance ≤ 100) :
  List.length (check_sqrt_accuracy scale tolerance numbers) = List.length numbers := sorry

theorem valid_results {scale tolerance : Int} {numbers : List Int} 
  (h1 : 0 < tolerance) (h2 : tolerance ≤ 100) :
  ∀ x ∈ check_sqrt_accuracy scale tolerance numbers, x = "yes" ∨ x = "no" := sorry

theorem negative_numbers_no {scale tolerance : Int} {numbers : List Int} 
  {n : Int} (h1 : 0 < tolerance) (h2 : tolerance ≤ 100) (h3 : n ∈ numbers) (h4 : n < 0) :
  ∀ i, List.get (check_sqrt_accuracy scale tolerance numbers) i = some "no" := sorry

theorem result_matches_tolerance {scale tolerance : Int} {numbers : List Int}
  {n : Int} (h1 : 0 < tolerance) (h2 : tolerance ≤ 100) (h3 : n ∈ numbers) (h4 : 0 ≤ n) :
  let sqrt_n := sqrt n
  let sqrt_squared := sqrt_n * sqrt_n
  let diff := (tolerance * n) / 100
  ∀ i, List.get (check_sqrt_accuracy scale tolerance numbers) i = 
    some (if n - sqrt_squared ≤ diff then "yes" else "no") := sorry

theorem zero_tolerance_perfect_squares {scale : Int} {numbers : List Int}
  {n : Int} (h1 : n ∈ numbers) :
  let sqrt_n := sqrt n
  ∀ i, List.get (check_sqrt_accuracy scale 0 numbers) i =
    some (if n ≥ 0 ∧ sqrt_n * sqrt_n = n then "yes" else "no") := sorry

theorem large_tolerance_all_yes {scale tolerance : Int} {numbers : List Int}
  (h1 : tolerance ≥ 100) (h2 : ∀ n ∈ numbers, n ≥ 0) :
  ∀ x ∈ check_sqrt_accuracy scale tolerance numbers, x = "yes" := sorry
-- </vc-theorems>
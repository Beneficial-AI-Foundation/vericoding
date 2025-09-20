-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_sums_occurrences (n : Nat) (queries : List Int) : List Nat :=
  sorry

-- Result should be same length as queries and contain naturals
-- </vc-definitions>

-- <vc-theorems>
theorem result_validity {n : Nat} {queries : List Int} :
  let result := count_sums_occurrences n queries 
  (result.length = queries.length) ∧ 
  (∀ x ∈ result, x ≥ 0) :=
  sorry

-- Special case for n=1

theorem n_equals_one {queries : List Int} :
  let result := count_sums_occurrences 1 queries
  ∀ (i : Nat), i < queries.length →
    result[i]! = (if queries[i]! = 2 then 1 else 0) :=
  sorry

-- Results never exceed n

theorem result_upper_bound {n : Nat} {queries : List Int} :
  let result := count_sums_occurrences n queries
  ∀ x ∈ result, x ≤ n :=
  sorry

-- Out of range queries give zero

theorem out_of_range_zero {n : Nat} {queries : List Int} :
  let result := count_sums_occurrences n queries
  ∀ (i : Nat), i < queries.length →
    (queries[i]! ≤ n + 1 ∨ queries[i]! > 3*n) → result[i]! = 0 :=
  sorry

-- Symmetry around 2n+1

theorem symmetry {n : Nat} {queries : List Int} :
  let result := count_sums_occurrences n queries
  let mid := 2*n + 1
  ∀ (i j : Nat), i < queries.length → j < queries.length →
    queries[i]! + queries[j]! = 2*mid → result[i]! = result[j]! :=
  sorry
-- </vc-theorems>
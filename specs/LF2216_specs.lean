-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveContestRating (n : Nat) (k : Int) (ratings : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solveContestRating_output_is_valid_indices
  (n : Nat) (k : Int) (ratings : List Nat)
  (h1 : 1 ≤ n ∧ n ≤ 100)
  (h2 : -1000 ≤ k ∧ k ≤ 1000)
  (h3 : ∀ r ∈ ratings, 1 ≤ r ∧ r ≤ 1000)
  (h4 : 1 ≤ ratings.length ∧ ratings.length ≤ 100) :
  let result := solveContestRating n k ratings
  ∀ x ∈ result, 1 ≤ x ∧ x ≤ n :=
  sorry

theorem solveContestRating_output_no_duplicates
  (n : Nat) (k : Int) (ratings : List Nat)
  (h1 : 1 ≤ n ∧ n ≤ 100)
  (h2 : -1000 ≤ k ∧ k ≤ 1000)
  (h3 : ∀ r ∈ ratings, 1 ≤ r ∧ r ≤ 1000)
  (h4 : 1 ≤ ratings.length ∧ ratings.length ≤ 100) :
  let result := solveContestRating n k ratings
  result.Nodup :=
  sorry

theorem solveContestRating_output_length_valid
  (n : Nat) (k : Int) (ratings : List Nat)
  (h1 : 1 ≤ n ∧ n ≤ 100)
  (h2 : -1000 ≤ k ∧ k ≤ 1000)
  (h3 : ∀ r ∈ ratings, 1 ≤ r ∧ r ≤ 1000)
  (h4 : 1 ≤ ratings.length ∧ ratings.length ≤ 100) :
  let result := solveContestRating n k ratings
  result.length ≤ n :=
  sorry

theorem solveContestRating_remaining_valid
  (n : Nat) (k : Int) (ratings : List Nat)
  (h1 : 1 ≤ n ∧ n ≤ 100)
  (h2 : -1000 ≤ k ∧ k ≤ 1000)
  (h3 : ∀ r ∈ ratings, 1 ≤ r ∧ r ≤ 1000)
  (h4 : 1 ≤ ratings.length ∧ ratings.length ≤ 100) :
  let result := solveContestRating n k ratings
  let remaining := List.range n |>.map (·+1) |>.filter (λ x => ¬result.contains x)
  remaining.length + result.length = n :=
  sorry
-- </vc-theorems>
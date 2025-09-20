-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_startups (n : Nat) (arr : List Int) : Nat :=
  sorry

def pow (base : Nat) (exp : Nat) (m : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_in_valid_range (n : Nat) (arr : List Int) (h₁ : n > 0) (h₂ : arr.length = n) :
  let result := solve_startups n arr
  0 ≤ result ∧ result < 1000000007 :=
sorry

theorem array_length_matches_n (n : Nat) (arr : List Int)
  (h₁ : n > 0) (h₂ : arr.length ≥ 1) :
  let truncated := (List.replicate n arr.head!).take n
  let result := solve_startups n truncated
  0 ≤ result ∧ result < 1000000007 :=
sorry
-- </vc-theorems>
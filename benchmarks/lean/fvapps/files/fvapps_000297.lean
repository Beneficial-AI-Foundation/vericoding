-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numFriendRequests (ages: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_nonnegative 
  (ages: List Nat)
  (h: ∀ x ∈ ages, 1 ≤ x ∧ x ≤ 120) :
  0 ≤ numFriendRequests ages :=
sorry

theorem single_age_no_requests
  (age: Nat)
  (h: 1 ≤ age ∧ age ≤ 120) :
  numFriendRequests [age] = 0 :=
sorry

theorem young_no_requests
  (ages: List Nat)
  (h1: ∀ x ∈ ages, 1 ≤ x ∧ x ≤ 120)
  (h2: ∀ x ∈ ages, x ≤ 14) :
  numFriendRequests ages = 0 :=
sorry

theorem identical_ages_requests
  (age: Nat)
  (h: 1 ≤ age ∧ age ≤ 120) :
  let n := 5
  if age ≥ 15 then
    numFriendRequests (List.replicate n age) = n * (n-1)
  else
    numFriendRequests (List.replicate n age) = 0 :=
sorry

theorem requests_symmetric
  (ages: List Nat)
  (h: ∀ x ∈ ages, 1 ≤ x ∧ x ≤ 120) :
  numFriendRequests ages = numFriendRequests ages.reverse :=
sorry
-- </vc-theorems>
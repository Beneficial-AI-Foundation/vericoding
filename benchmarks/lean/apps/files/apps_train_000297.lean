-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: 2
-/
-- #guard_msgs in
-- #eval numFriendRequests [16, 16]

/-
info: 2
-/
-- #guard_msgs in
-- #eval numFriendRequests [16, 17, 18]

/-
info: 3
-/
-- #guard_msgs in
-- #eval numFriendRequests [20, 30, 100, 110, 120]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded
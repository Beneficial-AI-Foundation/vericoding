-- <vc-preamble>
def MOD := 1000000007

def maxSumRangeQuery (nums : List Nat) (requests : List (Nat × Nat)) : Nat :=
  sorry

def listSum (l : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def listSortDescending (l : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxSumRangeQuery_bounded
  (nums : List Nat) 
  (requests : List (Nat × Nat))
  (h1 : nums.length > 0)
  (h2 : requests.length > 0)
  (h3 : ∀ r ∈ requests, r.1 ≤ r.2 ∧ r.2 < nums.length) :
  0 ≤ maxSumRangeQuery nums requests ∧ maxSumRangeQuery nums requests < MOD :=
  sorry 

theorem maxSumRangeQuery_deterministic
  (nums : List Nat)
  (requests : List (Nat × Nat))
  (h1 : nums.length > 0)
  (h2 : requests.length > 0)
  (h3 : ∀ r ∈ requests, r.1 ≤ r.2 ∧ r.2 < nums.length) :
  maxSumRangeQuery nums requests = maxSumRangeQuery nums requests :=
  sorry

theorem maxSumRangeQuery_single_request
  (nums : List Nat)
  (h : nums.length > 0) :
  let requests := [(0, nums.length - 1)]
  maxSumRangeQuery nums requests = (listSum nums) % MOD :=
  sorry

theorem maxSumRangeQuery_overlapping_bounds
  (nums : List Nat)
  (h1 : nums.length > 1) :
  let requests := [(0, nums.length / 2), (nums.length / 4, nums.length - 1)]
  let sorted_prefix := (listSortDescending nums).take nums.length
  maxSumRangeQuery nums requests ≤ (listSum sorted_prefix) * 2 % MOD :=
  sorry

/-
info: 19
-/
-- #guard_msgs in
-- #eval max_sum_range_query [1, 2, 3, 4, 5] [[1, 3], [0, 1]]

/-
info: 11
-/
-- #guard_msgs in
-- #eval max_sum_range_query [1, 2, 3, 4, 5, 6] [[0, 1]]

/-
info: 47
-/
-- #guard_msgs in
-- #eval max_sum_range_query [1, 2, 3, 4, 5, 10] [[0, 2], [1, 3], [1, 1]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded
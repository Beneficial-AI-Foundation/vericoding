-- <vc-preamble>
def valid_track (n : Nat) (track : Nat × Nat) : Prop :=
  let (u, v) := track
  1 ≤ u ∧ u ≤ n ∧ 1 ≤ v ∧ v ≤ n ∧ u ≠ v
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_ski_resort : List (Nat × Nat × List (Nat × Nat)) → List (Nat × List Nat) := sorry

theorem ski_resort_result_valid 
  (test_cases : List (Nat × Nat × List (Nat × Nat)))
  (h_nonempty : test_cases ≠ []) :
  let results := solve_ski_resort test_cases
  -- Results length matches input length
  results.length = test_cases.length ∧
  -- For each test case and result
  (∀ (tc : Nat × Nat × List (Nat × Nat)) (res : Nat × List Nat),
    tc ∈ test_cases → res ∈ results →
    let (n, m, tracks) := tc
    let (count, closed) := res
    -- Count equals length of closed list
    count = closed.length ∧
    -- All closed points are valid station numbers
    (∀ x ∈ closed, 1 ≤ x ∧ x ≤ n) ∧
    -- Closed points are unique
    closed.Nodup) := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ski_resort_input_bounds
  (test_cases : List (Nat × Nat × List (Nat × Nat)))
  (h_nonempty : test_cases ≠ []) :
  ∀ (n m : Nat) (tracks : List (Nat × Nat)),
  (n, m, tracks) ∈ test_cases →
  -- n is between 2 and 10
  2 ≤ n ∧ n ≤ 10 ∧
  -- m is between 0 and min(20, n*(n-1))
  0 ≤ m ∧ m ≤ min 20 (n*(n-1)) ∧
  -- tracks length equals m
  tracks.length = m ∧
  -- all tracks are valid
  (∀ t ∈ tracks, valid_track n t) := by sorry
-- </vc-theorems>
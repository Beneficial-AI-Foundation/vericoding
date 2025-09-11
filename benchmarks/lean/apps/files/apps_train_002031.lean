-- <vc-preamble>
def scheduleRepairs (requests : List (Nat × Nat)) : List (Nat × Nat) := sorry

def isNonOverlapping (intervals : List (Nat × Nat)) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def totalDurationPreserved (requests : List (Nat × Nat)) (result : List (Nat × Nat)) : Bool := sorry

def allPositive (intervals : List (Nat × Nat)) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem schedule_repairs_non_overlapping (requests : List (Nat × Nat)) : 
  let result := scheduleRepairs requests
  isNonOverlapping result = true := sorry

theorem schedule_repairs_preserves_duration (requests : List (Nat × Nat)) :
  let result := scheduleRepairs requests 
  totalDurationPreserved requests result = true := sorry

theorem schedule_repairs_all_positive (requests : List (Nat × Nat)) :
  let result := scheduleRepairs requests
  allPositive result = true := sorry

theorem schedule_repairs_preserves_length (requests : List (Nat × Nat)) :
  let result := scheduleRepairs requests
  result.length = requests.length := sorry

theorem schedule_repairs_handles_same_start (requests : List (Nat × Nat)) 
  (h : ∀ p ∈ requests, p.fst = 1) :
  let result := scheduleRepairs requests
  isNonOverlapping result = true ∧ totalDurationPreserved requests result = true := sorry

/-
info: [(9, 10), (1, 3), (4, 7)]
-/
-- #guard_msgs in
-- #eval schedule_repairs [(9, 2), (7, 3), (2, 4)]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval schedule_repairs [(1000000000, 1000000), (1000000000, 1000000), (100000000, 1000000), (1000000000, 1000000)]

/-
info: [(1, 5000000)]
-/
-- #guard_msgs in
-- #eval schedule_repairs [(1, 5000000)]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded
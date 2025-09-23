-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def scheduleRepairs (requests : List (Nat × Nat)) : List (Nat × Nat) :=
sorry

def isNonOverlapping (intervals : List (Nat × Nat)) : Bool :=
sorry

def totalDurationPreserved (requests : List (Nat × Nat)) (result : List (Nat × Nat)) : Bool :=
sorry

def allPositive (intervals : List (Nat × Nat)) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem schedule_repairs_non_overlapping (requests : List (Nat × Nat)) :
  let result := scheduleRepairs requests
  isNonOverlapping result = true :=
sorry

theorem schedule_repairs_preserves_duration (requests : List (Nat × Nat)) :
  let result := scheduleRepairs requests
  totalDurationPreserved requests result = true :=
sorry

theorem schedule_repairs_all_positive (requests : List (Nat × Nat)) :
  let result := scheduleRepairs requests
  allPositive result = true :=
sorry

theorem schedule_repairs_preserves_length (requests : List (Nat × Nat)) :
  let result := scheduleRepairs requests
  result.length = requests.length :=
sorry

theorem schedule_repairs_handles_same_start (requests : List (Nat × Nat))
  (h : ∀ p ∈ requests, p.fst = 1) :
  let result := scheduleRepairs requests
  isNonOverlapping result = true ∧ totalDurationPreserved requests result = true :=
sorry
-- </vc-theorems>
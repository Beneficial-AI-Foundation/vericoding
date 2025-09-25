-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def roundRobin (jobs : List Nat) (slice : Nat) (target : Nat) : Nat := sorry

def List.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + List.sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem roundRobin_lower_bound {jobs : List Nat} {slice : Nat} (h : jobs.length > 0) :
  roundRobin jobs slice 0 ≥ jobs.get! 0 := by sorry

theorem roundRobin_upper_bound {jobs : List Nat} {slice : Nat} (h : jobs.length > 0) :
  roundRobin jobs slice 0 ≤ List.sum jobs := by sorry

theorem roundRobin_single_job {job : Nat} {slice : Nat} :
  roundRobin [job] slice 0 = job := by sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval roundRobin [10] 4 0

/-
info: 15
-/
-- #guard_msgs in
-- #eval roundRobin [10, 20] 5 0

/-
info: 11
-/
-- #guard_msgs in
-- #eval roundRobin [10, 20, 1, 2, 3] 5 2
-- </vc-theorems>
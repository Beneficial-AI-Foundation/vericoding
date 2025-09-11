-- <vc-preamble>
def sum_nat_list : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + sum_nat_list xs
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def exclusive_time (n : Nat) (logs : List String) : List Nat := sorry

theorem exclusive_time_nonnegative {n : Nat} {logs : List String} :
  ∀ t, t ∈ exclusive_time n logs → t ≥ 0
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem exclusive_time_edge_cases :
  exclusive_time 0 [] = [] ∧
  exclusive_time 1 [] = [] ∧ 
  exclusive_time 0 ["0:start:0"] = []
  := sorry

/-
info: [3, 4]
-/
-- #guard_msgs in
-- #eval exclusive_time 2 ["0:start:0", "1:start:2", "1:end:5", "0:end:6"]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval exclusive_time 1 ["0:start:0", "0:end:0"]

/-
info: [2, 2]
-/
-- #guard_msgs in
-- #eval exclusive_time 2 ["0:start:0", "1:start:1", "1:end:2", "0:end:3"]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
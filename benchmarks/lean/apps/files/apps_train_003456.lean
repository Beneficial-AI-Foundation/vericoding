-- <vc-preamble>
def distribute (nodes : Nat) (workload : Nat) : List (List Nat) :=
  sorry

def listMaximum (l : List Nat) : Nat :=
  sorry

def listMinimum (l : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def listSum (l : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem distribute_length {nodes workload : Nat} 
  (h : nodes ≤ workload ∨ workload = 0) :
  (distribute nodes workload).length = nodes :=
  sorry

/-
info: [[0, 1], [2, 3]]
-/
-- #guard_msgs in
-- #eval distribute 2 4

/-
info: [[0], [1], [2]]
-/
-- #guard_msgs in
-- #eval distribute 3 3

/-
info: [[0, 1, 2], [3, 4, 5], [6, 7], [8, 9]]
-/
-- #guard_msgs in
-- #eval distribute 4 10
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
-- <vc-preamble>
def SJF (jobs : List Nat) (index : Nat) : Nat :=
  sorry

abbrev sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def filterWithIndex (l : List Nat) (p : Nat → Nat → Bool) : List Nat :=
  let rec helper : List Nat → Nat → List Nat
    | [], _ => []
    | (x :: xs), i => if p i x then x :: helper xs (i+1) else helper xs (i+1)
  helper l 0
-- </vc-definitions>

-- <vc-theorems>
theorem single_job_returns_itself {jobs : List Nat} {job : Nat} (h : jobs = [job]) :
  SJF jobs 0 = job :=
  sorry

/-
info: 100
-/
-- #guard_msgs in
-- #eval SJF [100] 0

/-
info: 6
-/
-- #guard_msgs in
-- #eval SJF [3, 10, 20, 1, 2] 0

/-
info: 16
-/
-- #guard_msgs in
-- #eval SJF [3, 10, 10, 20, 1, 2] 1
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
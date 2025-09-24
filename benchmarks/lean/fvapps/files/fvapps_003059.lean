-- <vc-preamble>
abbrev sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs

def filterWithIndex (l : List Nat) (p : Nat → Nat → Bool) : List Nat :=
  let rec helper : List Nat → Nat → List Nat
    | [], _ => []
    | (x :: xs), i => if p i x then x :: helper xs (i+1) else helper xs (i+1)
  helper l 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SJF (jobs : List Nat) (index : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_job_returns_itself {jobs : List Nat} {job : Nat} (h : jobs = [job]) :
  SJF jobs 0 = job :=
sorry
-- </vc-theorems>
-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length ≥ 1

def count_mismatches_up_to (s : String) (limit : Nat) : Nat :=
  if limit = 0 then 0
  else 
    let n := s.length - 1
    let idx1 := limit - 1
    let idx2 := n - (limit - 1)
    let mismatch := if s.data.get! idx1 ≠ s.data.get! idx2 then 1 else 0
    count_mismatches_up_to s (limit - 1) + mismatch

def count_mismatches (s : String) : Nat :=
  count_mismatches_up_to s s.length

def ValidResult (s : String) (result : Int) : Prop :=
  result ≥ 0 ∧ result ≤ s.length / 2 ∧ result = (count_mismatches s / 2 : Int)

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : Int) (h_precond : solve_precond s) : Prop :=
  ValidResult s result

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>
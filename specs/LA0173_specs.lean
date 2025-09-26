-- <vc-preamble>
def IsPowerOfTwo : Int → Bool
  | n => if n ≤ 0 then false
         else if n = 1 then true
         else if n % 2 = 1 then false
         else IsPowerOfTwo (n / 2)
termination_by n => n.natAbs
decreasing_by 
  simp_wf
  omega

def ValidInput (n : Int) : Prop :=
  n ≥ 1

def CorrectResult (n : Int) (result : Int) : Prop :=
  if n % 2 = 1 then 
    result = (n - 1) / 2
  else 
    ∃ z, 1 ≤ z ∧ z ≤ n ∧ IsPowerOfTwo z ∧ z ≤ n ∧ z * 2 > n ∧ result = (n - z) / 2

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (_ : solve_precond n) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  CorrectResult n result

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>
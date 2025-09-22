-- <vc-preamble>
def SumOfDigits (x : Nat) : Nat :=
  if x = 0 then 0
  else (x % 10) + SumOfDigits (x / 10)

def Check (x s : Int) : Bool :=
  x - (SumOfDigits x.natAbs) ≥ s

@[reducible, simp]
def solve_precond (n s : Int) : Prop :=
  n ≥ 1 ∧ s ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n s : Int) (h_precond : solve_precond n s) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n s : Int) (result : Int) (h_precond : solve_precond n s) : Prop :=
  result ≥ 0 ∧ result ≤ n ∧ result = ((List.map Int.ofNat (List.range n.natAbs)).filter (fun x => 1 ≤ x ∧ x ≤ n ∧ Check x s = true)).length

theorem solve_spec_satisfied (n s : Int) (h_precond : solve_precond n s) :
    solve_postcond n s (solve n s h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- <vc-preamble>
def ValidInput (N : Int) : Bool :=
  N ≥ 0

partial def FactorsInFactorial (n p : Int) : Int :=
  if n = 0 then 0
  else n / p + FactorsInFactorial (n / p) p

partial def FactorsInDoubleFactorial (n p : Int) : Int :=
  if n ≤ 0 then 0
  else if n % 2 = 1 then
    FactorsInFactorial n p - FactorsInDoubleFactorial (n - 1) p
  else
    FactorsInFactorial (n / 2) p + (if p = 2 then n / 2 else 0)

def ValidResult (N result : Int) : Prop :=
  result ≥ 0 ∧
  result = (if FactorsInDoubleFactorial N 2 < FactorsInDoubleFactorial N 5 then FactorsInDoubleFactorial N 2 else FactorsInDoubleFactorial N 5)

@[reducible, simp]
def solve_precond (N : Int) : Prop :=
  ValidInput N = true
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (h_precond : solve_precond N) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (result : Int) (h_precond : solve_precond N) : Prop :=
  ValidResult N result

theorem solve_spec_satisfied (N : Int) (h_precond : solve_precond N) :
    solve_postcond N (solve N h_precond) h_precond := by
  sorry
-- </vc-theorems>
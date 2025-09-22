-- <vc-preamble>
def ValidInput (A B : Int) : Prop :=
  A > 0 ∧ B > 0

partial def gcd (a b : Int) : Int :=
  if b = 0 then a else gcd b (a % b)

partial def divideOutFactor (n factor : Int) : Int :=
  let next := n / factor
  if next % factor = 0 then divideOutFactor next factor else next

partial def countDistinctPrimeFactorsHelper (n i : Int) : Int :=
  if i * i > n then
    if n > 1 then 1 else 0
  else if n % i = 0 then
    1 + countDistinctPrimeFactorsHelper (divideOutFactor n i) (i + 1)
  else
    countDistinctPrimeFactorsHelper n (i + 1)

def countDistinctPrimeFactors (n : Int) : Int :=
  if n = 1 then 0 else countDistinctPrimeFactorsHelper n 2

def CorrectResult (A B result : Int) : Prop :=
  result = countDistinctPrimeFactors (gcd A B) + 1

@[reducible, simp]
def solve_precond (A B : Int) : Prop :=
  ValidInput A B
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (A B : Int) (h_precond : solve_precond A B) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B : Int) (result : Int) (h_precond : solve_precond A B) : Prop :=
  result > 0 ∧ CorrectResult A B result

theorem solve_spec_satisfied (A B : Int) (h_precond : solve_precond A B) :
    solve_postcond A B (solve A B h_precond) h_precond := by
  sorry
-- </vc-theorems>
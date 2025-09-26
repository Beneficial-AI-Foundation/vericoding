-- <vc-preamble>
partial def CountNonZeroDigits (n : Int) : Int :=
  if n = 0 then 0
  else if n % 10 = 0 then CountNonZeroDigits (n / 10)
  else 1 + CountNonZeroDigits (n / 10)

partial def CountRange (n k start end_ : Int) : Int :=
  if start > end_ then 0
  else if CountNonZeroDigits start = k then 
      1 + CountRange n k (start + 1) end_
  else 
      CountRange n k (start + 1) end_

def CountNumbersWithKNonZeroDigits (n k : Int) : Int :=
  CountRange n k 1 n

def ValidInput (n k : Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1 ∧ k ≤ 3

@[reducible, simp]
def solve_precond (N K : Int) : Prop :=
  ValidInput N K
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N K : Int) (h_precond : solve_precond N K) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N K : Int) (count: Int) (h_precond : solve_precond N K) : Prop :=
  count = CountNumbersWithKNonZeroDigits N K ∧ count ≥ 0 ∧ count ≤ N

theorem solve_spec_satisfied (N K : Int) (h_precond : solve_precond N K) :
    solve_postcond N K (solve N K h_precond) h_precond := by
  sorry
-- </vc-theorems>
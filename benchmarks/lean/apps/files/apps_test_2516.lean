-- <vc-preamble>
def isPrime (p : Int) : Prop :=
  p ≥ 2 ∧ ∀ k, 2 ≤ k ∧ k < p → p % k ≠ 0

def ValidInput (n p : Int) (s : String) : Prop :=
  n ≥ 1 ∧
  p ≥ 2 ∧
  isPrime p ∧
  s.length = n.natAbs ∧
  ∀ i, 0 ≤ i ∧ i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9'

def substringToInt (s : String) : Int :=
  s.data.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def ValidResult (result n : Int) : Prop :=
  result ≥ 0 ∧ result ≤ n * (n + 1) / 2

@[reducible, simp]
def solve_precond (n p : Int) (s : String) : Prop :=
  ValidInput n p s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n p : Int) (s : String) (h_precond : solve_precond n p s) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n p : Int) (s : String) (result : Int) (h_precond : solve_precond n p s) : Prop :=
  ValidResult result n

theorem solve_spec_satisfied (n p : Int) (s : String) (h_precond : solve_precond n p s) :
    solve_postcond n p s (solve n p s h_precond) h_precond := by
  sorry
-- </vc-theorems>
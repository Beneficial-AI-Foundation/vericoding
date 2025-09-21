-- <vc-preamble>
def ValidInput (n : Int) (ar : List Int) : Prop :=
  n ≥ 2 ∧ ar.length = n.natAbs ∧ ∀ i, 0 ≤ i ∧ i < n.natAbs → ar[i]! > 0

partial def GCD (x y : Int) : Int :=
  if x = y then x
  else if x < y then GCD x (y - x)
  else GCD (x - y) y

partial def GCDOfSequence (ar : List Int) : Int :=
  match ar with
  | [] => 1
  | [x] => x
  | x :: xs => GCD x (GCDOfSequence xs)

def MinimalSum (n : Int) (ar : List Int) : Int :=
  GCDOfSequence ar * n

@[reducible, simp]
def solve_precond (n : Int) (ar : List Int) : Prop :=
  ValidInput n ar
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (ar : List Int) (h_precond : solve_precond n ar) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (ar : List Int) (result : Int) (h_precond : solve_precond n ar) : Prop :=
  result = MinimalSum n ar ∧ result > 0

theorem solve_spec_satisfied (n : Int) (ar : List Int) (h_precond : solve_precond n ar) :
    solve_postcond n ar (solve n ar h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- <vc-preamble>
@[reducible, simp]
def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧ a.length = n.natAbs

def CountLocalExtrema (n : Int) (a : List Int) (h : ValidInput n a) : Int :=
  let validIndices := List.range (n.natAbs - 2) |>.map (· + 1)
  let extremaIndices := validIndices.filter (fun i =>
    i < a.length ∧ i > 0 ∧ i + 1 < a.length ∧
    ((a[i]! > a[i-1]! ∧ a[i]! > a[i+1]!) ∨ (a[i]! < a[i-1]! ∧ a[i]! < a[i+1]!)))
  extremaIndices.length

def IsLocalExtremum (a : List Int) (i : Int) : Prop :=
  0 ≤ i ∧ i < a.length ∧ 1 ≤ i ∧ i < a.length - 1 ∧ 
  ((a[i.natAbs]! > a[i.natAbs-1]! ∧ a[i.natAbs]! > a[i.natAbs+1]!) ∨ 
   (a[i.natAbs]! < a[i.natAbs-1]! ∧ a[i.natAbs]! < a[i.natAbs+1]!))

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : List Int) (h_precond : solve_precond n a) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (result : Int) (h_precond : solve_precond n a) : Prop :=
  result ≥ 0 ∧ 
  (n ≤ 2 → result = 0) ∧
  (n > 2 → result ≤ n - 2) ∧
  result = CountLocalExtrema n a h_precond

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>
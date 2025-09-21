-- <vc-preamble>

def ValidInput (n m : Int) (pairs : List (Int × Int)) : Prop :=
  n ≥ 2 ∧ 
  m ≥ 0 ∧ 
  pairs.length = m ∧
  (∀ i, 0 ≤ i ∧ i < pairs.length → 1 ≤ (pairs[i]!).1 ∧ (pairs[i]!).1 ≤ n ∧ 1 ≤ (pairs[i]!).2 ∧ (pairs[i]!).2 ≤ n) ∧
  (∀ i, 0 ≤ i ∧ i < pairs.length → (pairs[i]!).1 ≠ (pairs[i]!).2)

def computeFinalL (pairs : List (Int × Int)) : Int :=
  match pairs with
  | [] => 1
  | _ :: rest => 
    let x := (pairs[pairs.length-1]!).1
    let y := (pairs[pairs.length-1]!).2
    let minVal := if x < y then x else y
    let restL := computeFinalL rest
    if restL > minVal then restL else minVal

def computeFinalR (n : Int) (pairs : List (Int × Int)) : Int :=
  match pairs with
  | [] => n
  | _ :: rest =>
    let x := (pairs[pairs.length-1]!).1
    let y := (pairs[pairs.length-1]!).2
    let maxVal := if x > y then x else y
    let restR := computeFinalR n rest
    if restR < maxVal then restR else maxVal

def myMax (a b : Int) : Int :=
  if a > b then a else b

def ValidResult (n : Int) (pairs : List (Int × Int)) (result : Int) : Prop :=
  result ≥ 0 ∧
  result ≤ n - 1 ∧
  result = myMax (computeFinalR n pairs - computeFinalL pairs) 0

@[reducible, simp]
def solve_precond (n m : Int) (pairs : List (Int × Int)) : Prop :=
  ValidInput n m pairs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (pairs : List (Int × Int)) (h_precond : solve_precond n m pairs) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (pairs : List (Int × Int)) (result : Int) (h_precond : solve_precond n m pairs) : Prop :=
  ValidResult n pairs result

theorem solve_spec_satisfied (n m : Int) (pairs : List (Int × Int)) (h_precond : solve_precond n m pairs) :
    solve_postcond n m pairs (solve n m pairs h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- <vc-preamble>
def intToDigitsHelper (x : Nat) : List Nat :=
  if x < 10 then [x]
  else intToDigitsHelper (x / 10) ++ [x % 10]
termination_by x

def intToDigits (x : Int) : List Int :=
  if x = 0 then [0]
  else (intToDigitsHelper x.natAbs).map Int.ofNat

def digitSum (digits : List Int) : Int :=
  digits.sum

def ValidInput (x : Int) : Prop :=
  x ≥ 1

def ValidResult (x : Int) (result : Int) : Prop :=
  result > 0 ∧
  result ≤ x ∧
  (∀ y, 1 ≤ y ∧ y ≤ x → digitSum (intToDigits y) ≤ digitSum (intToDigits result)) ∧
  (∀ y, 1 ≤ y ∧ y ≤ x ∧ digitSum (intToDigits y) = digitSum (intToDigits result) → y ≤ result)

@[reducible, simp]
def solve_precond (x : Int) : Prop :=
  ValidInput x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x : Int) (h_precond : solve_precond x) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x : Int) (result : Int) (h_precond : solve_precond x) : Prop :=
  ValidResult x result

theorem solve_spec_satisfied (x : Int) (h_precond : solve_precond x) :
    solve_postcond x (solve x h_precond) h_precond := by
  sorry
-- </vc-theorems>
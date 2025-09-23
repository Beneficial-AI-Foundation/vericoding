-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  a > 1 ∧ b ≥ 0

def SocketsAfterStrips (strips a : Int) : Int :=
  1 + strips * (a - 1)

def CeilingDivision (x y : Int) : Int :=
  if x % y = 0 then x / y
  else if x ≥ 0 then x / y + 1
  else x / y

def MinStripsNeeded (a b : Int) : Int :=
  if b ≤ 1 then 0
  else CeilingDivision (b - 1) (a - 1)

def CorrectResult (a b result : Int) : Prop :=
  result ≥ 0 ∧
  SocketsAfterStrips result a ≥ b ∧
  (result = 0 ∨ SocketsAfterStrips (result - 1) a < b)

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result: Int) (h_precond : solve_precond a b) : Prop :=
  CorrectResult a b result

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  sorry
-- </vc-theorems>
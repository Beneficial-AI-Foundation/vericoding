-- <vc-preamble>
def ValidInput (a b c d : Int) : Prop :=
  a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0

def IsValidFractionString (s : String) (num den : Int) : Prop :=
  num ≥ 0 ∧ den > 0 ∧ 
  Int.gcd num den = 1 ∧
  s = toString num ++ "/" ++ toString den

@[reducible, simp]
def solve_precond (a b c d : Int) : Prop :=
  ValidInput a b c d
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c d : Int) (h_precond : solve_precond a b c d) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c d : Int) (result : String) (h_precond : solve_precond a b c d) : Prop :=
  (a * d = b * c → result = "0/1") ∧
  (a * d > b * c → ∃ numerator denominator, 
      numerator > 0 ∧ denominator > 0 ∧ 
      Int.gcd numerator denominator = 1 ∧
      result = toString numerator ++ "/" ++ toString denominator ∧
      numerator * a * d = (a * d - b * c) * denominator) ∧
  (a * d < b * c → ∃ numerator denominator, 
      numerator > 0 ∧ denominator > 0 ∧ 
      Int.gcd numerator denominator = 1 ∧
      result = toString numerator ++ "/" ++ toString denominator ∧
      numerator * b * c = (b * c - a * d) * denominator)

theorem solve_spec_satisfied (a b c d : Int) (h_precond : solve_precond a b c d) :
    solve_postcond a b c d (solve a b c d h_precond) h_precond := by
  sorry
-- </vc-theorems>
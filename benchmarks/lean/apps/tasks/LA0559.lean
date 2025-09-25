-- <vc-preamble>
def ValidInput (trainFare busFare : Int) : Prop :=
  1 ≤ trainFare ∧ trainFare ≤ 100 ∧ 1 ≤ busFare ∧ busFare ≤ 100 ∧ busFare % 2 = 0

def TotalCost (trainFare busFare : Int) : Int :=
  trainFare + busFare / 2

-- String utility functions (assumed to exist)
axiom split : String → Char → List String
axiom replace : String → String → String → String
axiom isValidInteger : String → Bool
axiom stringToInt : String → Int
axiom intToString : Int → String

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧
  (∃ i, 0 ≤ i ∧ i < input.length ∧ input.data[i]! = ' ') ∧
  (let parts := split (replace input "\n" "") ' ';
   parts.length ≥ 2 ∧ 
   isValidInteger (parts[0]!) ∧ 
   isValidInteger (parts[1]!)) ∧
  (let parts := split (replace input "\n" "") ' ';
   let trainFare := stringToInt (parts[0]!);
   let busFare := stringToInt (parts[1]!);
   ValidInput trainFare busFare)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length > 0 ∧
  result.data[result.length - 1]! = '\n' ∧
  (let parts := split (replace input "\n" "") ' ';
   let trainFare := stringToInt (parts[0]!);
   let busFare := stringToInt (parts[1]!);
   result = intToString (TotalCost trainFare busFare) ++ "\n")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length ≥ 0

def ValidTestCase (n a b c d : Int) : Prop :=
  n ≥ 1 ∧ n ≤ 1000 ∧
  a ≥ 0 ∧ a ≤ 1000 ∧
  b ≥ 0 ∧ b < a ∧
  c ≥ 0 ∧ c ≤ 1000 ∧
  d ≥ 0 ∧ d < c

def CanAchieveWeight (n a b c d : Int) : Bool :=
  let minWeight := (a - b) * n
  let maxWeight := (a + b) * n
  let targetMin := c - d
  let targetMax := c + d
  !(minWeight > targetMax || maxWeight < targetMin)

def ValidOutput (output : String) : Prop :=
  ∀ i, 0 ≤ i ∧ i < output.length → output.data[i]! ∈ ['Y', 'e', 's', 'N', 'o', '\n']

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
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
  ValidOutput result ∧
  ((input = "" ∨ input = "\n") → result = "") ∧
  (input ≠ "" ∧ input ≠ "\n" → (result.length > 0 → 
    (if h : result.length > 0 then result.data[result.length - 1]! = '\n' else False) ∨ 
    (result.length > 3 ∧ (result.drop (result.length - 4) = "Yes\n" ∨ result.drop (result.length - 3) = "No\n"))))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
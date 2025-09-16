-- <vc-preamble>
-- <vc-preamble>
def isValidInteger (s : String) : Prop := sorry

def parseInt (s : String) : Int := sorry

def findSpace (s : String) : Nat := sorry

def intToString (n : Int) : String := sorry

def getAString (input : String) : String := sorry

def getBString (input : String) : String := sorry

def getA (input : String) : Int := sorry

def getB (input : String) : Int := sorry

def ValidInput (input : String) : Prop :=
  input.length ≥ 3 ∧
  ∃ spacePos, 0 < spacePos ∧ spacePos < input.length - 1 ∧ input.data[spacePos]! = ' ' ∧
  (∀ i, 0 ≤ i ∧ i < spacePos → input.data[i]! ≠ ' ') ∧
  (∀ i, spacePos + 1 ≤ i ∧ i < input.length → input.data[i]! ≠ ' ' ∨ input.data[i]! = '\n') ∧
  isValidInteger (getAString input) ∧ isValidInteger (getBString input) ∧
  -100 ≤ getA input ∧ getA input ≤ 100 ∧ -100 ≤ getB input ∧ getB input ≤ 100

def max3 (a b c : Int) : Int :=
  if a ≥ b ∧ a ≥ c then a
  else if b ≥ c then b
  else c

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  let maxVal := max3 (getA input + getB input) (getA input - getB input) (getA input * getB input)
  result = intToString maxVal ++ "\n" ∧
  -10000 ≤ maxVal ∧ maxVal ≤ 10000

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>

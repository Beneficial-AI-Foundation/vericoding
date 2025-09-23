-- <vc-preamble>
def ValidInput (a b c : Int) : Prop :=
  1 ≤ b ∧ b ≤ a ∧ a ≤ 20 ∧ 1 ≤ c ∧ c ≤ 20

def RemainingWater (a b c : Int) : Int :=
  let availableSpace := a - b
  let remaining := c - availableSpace
  if remaining ≥ 0 then remaining else 0

-- String manipulation functions (assumed to exist)
axiom SplitOnSpaces : String → List String
axiom StringToInt : String → Int
axiom IntToString : Int → String

def hasNewline (s : String) : Bool :=
  s.length > 0 && s.data[s.length.pred]! = '\n'

def removeNewline (s : String) : String :=
  if hasNewline s then s.extract 0 ⟨s.length.pred⟩ else s

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧
  (let trimmed := removeNewline input
   let parts := SplitOnSpaces trimmed
   parts.length = 3) ∧
  (let trimmed := removeNewline input
   let parts := SplitOnSpaces trimmed
   parts.length = 3 →
   (∀ i, 0 ≤ i ∧ i < (parts[0]!).length → '0' ≤ (parts[0]!).data[i]! ∧ (parts[0]!).data[i]! ≤ '9') ∧
   (∀ i, 0 ≤ i ∧ i < (parts[1]!).length → '0' ≤ (parts[1]!).data[i]! ∧ (parts[1]!).data[i]! ≤ '9') ∧
   (∀ i, 0 ≤ i ∧ i < (parts[2]!).length → '0' ≤ (parts[2]!).data[i]! ∧ (parts[2]!).data[i]! ≤ '9') ∧
   (parts[0]!).length > 0 ∧ (parts[1]!).length > 0 ∧ (parts[2]!).length > 0) ∧
  (let trimmed := removeNewline input
   let parts := SplitOnSpaces trimmed
   parts.length = 3 →
   ValidInput (StringToInt (parts[0]!)) (StringToInt (parts[1]!)) (StringToInt (parts[2]!)))
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (_ : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (_ : solve_precond input) : Prop :=
  result.length > 0 ∧
  result.data[result.length.pred]! = '\n' ∧
  (let trimmed := removeNewline input
   let parts := SplitOnSpaces trimmed
   let a := StringToInt (parts[0]!)
   let b := StringToInt (parts[1]!)
   let c := StringToInt (parts[2]!)
   result = IntToString (RemainingWater a b c) ++ "\n")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- <vc-preamble>
def findSpace (s : String) : Nat :=
  let chars := s.toList
  let rec helper (i : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => s.length
    | fuel' + 1 =>
      match chars[i]? with
      | none => s.length
      | some c => if c = ' ' then i else helper (i + 1) fuel'
  helper 0 s.length

def parseInt (s : String) : Int :=
  s.toInt?.getD 0

def isValidInteger (s : String) : Prop :=
  s.toInt?.isSome

def getAString (input : String) : String :=
  let trimmed := if input.length > 0 ∧ input.toList.getLast? = some '\n' 
                 then input.take (input.length - 1)
                 else input
  let spaceIndex := findSpace trimmed
  trimmed.take spaceIndex

def getBString (input : String) : String :=
  let trimmed := if input.length > 0 ∧ input.toList.getLast? = some '\n' 
                 then input.take (input.length - 1)
                 else input
  let spaceIndex := findSpace trimmed
  trimmed.drop (spaceIndex + 1)

def getA (input : String) : Int :=
  parseInt (getAString input)

def getB (input : String) : Int :=
  parseInt (getBString input)

def ValidInput (input : String) : Prop :=
  input.length ≥ 3 ∧
  ∃ spacePos, 0 < spacePos ∧ spacePos < input.length - 1 ∧ 
    input.toList[spacePos]? = some ' ' ∧
    (∀ i, 0 ≤ i ∧ i < spacePos → input.toList[i]? ≠ some ' ') ∧
    (∀ i, spacePos + 1 ≤ i ∧ i < input.length → 
      input.toList[i]? ≠ some ' ' ∨ input.toList[i]? = some '\n') ∧
    isValidInteger (getAString input) ∧ isValidInteger (getBString input) ∧
    -100 ≤ getA input ∧ getA input ≤ 100 ∧ -100 ≤ getB input ∧ getB input ≤ 100

def max3 (a b c : Int) : Int :=
  if a ≥ b ∧ a ≥ c then a
  else if b ≥ c then b
  else c

def intToString (n : Int) : String := toString n

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
  let maxVal := max3 (getA input + getB input) (getA input - getB input) (getA input * getB input)
  result = intToString maxVal ++ "\n" ∧
  -10000 ≤ maxVal ∧ maxVal ≤ 10000

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
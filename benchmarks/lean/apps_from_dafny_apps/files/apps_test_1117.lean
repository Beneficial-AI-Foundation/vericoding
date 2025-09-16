-- <vc-preamble>
-- <vc-preamble>
def myMin (a b : Int) : Int :=
  if a ≤ b then a else b

def myMax (a b : Int) : Int :=
  if a ≥ b then a else b

def split (input : String) (delimiter : Char) : List String :=
  sorry

def parseInt (s : String) : Int :=
  sorry

def parseRectanglesFromLines (lines : List String) (n : Int) : List (Int × Int) :=
  sorry

def parseRectangles (input : String) : List (Int × Int) :=
  let lines := split input '\n'
  if lines.length = 0 then []
  else
    let n := parseInt (lines[0]!)
    if n ≤ 0 then []
    else parseRectanglesFromLines (lines.drop 1) n

def canFormNonAscendingSequenceHelper (rectangles : List (Int × Int)) (index : Nat) (prevHeight : Int) : Bool :=
  if index ≥ rectangles.length then true
  else
    let a := rectangles[index]!.1
    let b := rectangles[index]!.2
    let minDim := myMin a b
    let maxDim := myMax a b
    if minDim > prevHeight then false
    else if minDim ≤ prevHeight ∧ prevHeight < maxDim then 
      canFormNonAscendingSequenceHelper rectangles (index + 1) minDim
    else 
      canFormNonAscendingSequenceHelper rectangles (index + 1) maxDim

def canFormNonAscendingSequence (rectangles : List (Int × Int)) : Bool :=
  if rectangles.length ≤ 1 then true
  else canFormNonAscendingSequenceHelper rectangles 1 (myMax rectangles[0]!.1 rectangles[0]!.2)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
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
  (result = "YES" ∨ result = "NO") ∧ 
  (result = "YES" ↔ canFormNonAscendingSequence (parseRectangles input))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>

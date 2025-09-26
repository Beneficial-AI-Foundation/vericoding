import Mathlib
-- <vc-preamble>
def minInt (a b : Int) : Int :=
  if a ≤ b then a else b

def maxInt (a b : Int) : Int :=
  if a ≥ b then a else b

def parseInt (_ : String) : Int :=
  0  -- placeholder implementation

def split (_ : String) (_ : Char) : List String :=
  []  -- placeholder implementation

def parseRectanglesFromLines (_ : List String) (_ : Int) : List (Int × Int) :=
  []  -- placeholder implementation

def parseRectangles (input : String) : List (Int × Int) :=
  let lines := split input '\n'
  if lines.length = 0 then []
  else
    let n := parseInt (lines[0]!)
    if n ≤ 0 then []
    else parseRectanglesFromLines (lines.drop 1) n

def canFormNonAscendingSequenceHelper (rectangles : List (Int × Int)) (index : Nat) (prevHeight : Int) : Bool :=
  if h : index < rectangles.length then
    let a := (rectangles.get ⟨index, h⟩).1
    let b := (rectangles.get ⟨index, h⟩).2
    let minDim := minInt a b
    let maxDim := maxInt a b
    if minDim > prevHeight then false
    else if minDim ≤ prevHeight ∧ prevHeight < maxDim then 
      canFormNonAscendingSequenceHelper rectangles (index + 1) minDim
    else 
      canFormNonAscendingSequenceHelper rectangles (index + 1) maxDim
  else
    true
termination_by rectangles.length - index

def canFormNonAscendingSequence (rectangles : List (Int × Int)) : Bool :=
  if rectangles.length ≤ 1 then true
  else 
    if h : 0 < rectangles.length then
      canFormNonAscendingSequenceHelper rectangles 1 (maxInt (rectangles.get ⟨0, h⟩).1 (rectangles.get ⟨0, h⟩).2)
    else
      true

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  if canFormNonAscendingSequence (parseRectangles input) then "YES" else "NO"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (_ : solve_precond input) : Prop :=
  (result = "YES" ∨ result = "NO") ∧ 
  (result = "YES" ↔ canFormNonAscendingSequence (parseRectangles input))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  classical
  cases h : canFormNonAscendingSequence (parseRectangles input) <;>
    simp [solve_postcond, solve, h]
-- </vc-theorems>

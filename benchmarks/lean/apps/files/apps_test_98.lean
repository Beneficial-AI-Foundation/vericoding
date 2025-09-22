-- <vc-preamble>
def IsValidInt (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9'

def SplitLinesHelper (s : String) (i : Nat) (current : String) (lines : List String) : List String :=
  if i ≥ s.length then
    if current.length > 0 then lines ++ [current] else lines
  else if h : i < s.length then
    if s.data[i]! = '\n' then
      if current.length > 0 then 
        SplitLinesHelper s (i+1) "" (lines ++ [current])
      else 
        SplitLinesHelper s (i+1) "" lines
    else
      SplitLinesHelper s (i+1) (current ++ s.data[i]!.toString) lines
  else
    lines

def SplitLinesFunc (s : String) : List String :=
  if s.length = 0 then []
  else SplitLinesHelper s 0 "" []

def SplitSpacesHelper (s : String) (i : Nat) (current : String) (parts : List String) : List String :=
  if i ≥ s.length then
    if current.length > 0 then parts ++ [current] else parts
  else if h : i < s.length then
    if s.data[i]! = ' ' ∨ s.data[i]! = '\t' then
      if current.length > 0 then 
        SplitSpacesHelper s (i+1) "" (parts ++ [current])
      else 
        SplitSpacesHelper s (i+1) "" parts
    else
      SplitSpacesHelper s (i+1) (current ++ s.data[i]!.toString) parts
  else
    parts

def SplitSpacesFunc (s : String) : List String :=
  if s.length = 0 then []
  else SplitSpacesHelper s 0 "" []

def ParseIntHelper (s : String) (i : Nat) (acc : Nat) : Nat :=
  if i ≥ s.length then acc
  else if h : i < s.length then
    ParseIntHelper s (i+1) (acc * 10 + (s.data[i]!.toNat - '0'.toNat))
  else
    acc

def ParseIntFunc (s : String) : Int :=
  Int.ofNat (ParseIntHelper s 0 0)

def ValidInput (input : String) : Prop :=
  let lines := SplitLinesFunc input
  lines.length ≥ 3 ∧
  let boardParts := SplitSpacesFunc (lines[0]!)
  let paint1Parts := SplitSpacesFunc (lines[1]!)
  let paint2Parts := SplitSpacesFunc (lines[2]!)
  boardParts.length ≥ 2 ∧ paint1Parts.length ≥ 2 ∧ paint2Parts.length ≥ 2 ∧
  IsValidInt (boardParts[0]!) ∧ IsValidInt (boardParts[1]!) ∧
  IsValidInt (paint1Parts[0]!) ∧ IsValidInt (paint1Parts[1]!) ∧
  IsValidInt (paint2Parts[0]!) ∧ IsValidInt (paint2Parts[1]!)

def CanPlaceBothPaintings (a b c d e f : Int) : Prop :=
  (c + e ≤ a ∧ max d f ≤ b) ∨
  (c + e ≤ b ∧ max d f ≤ a) ∨
  (c + f ≤ a ∧ max d e ≤ b) ∨
  (c + f ≤ b ∧ max d e ≤ a) ∨
  (d + e ≤ a ∧ max c f ≤ b) ∨
  (d + e ≤ b ∧ max c f ≤ a) ∨
  (d + f ≤ a ∧ max c e ≤ b) ∨
  (d + f ≤ b ∧ max c e ≤ a)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
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
  (result = "YES\n" ∨ result = "NO\n" ∨ result = "") ∧
  (ValidInput input → 
    (result = "YES\n" ↔ 
      let lines := SplitLinesFunc input
      let boardParts := SplitSpacesFunc (lines[0]!)
      let paint1Parts := SplitSpacesFunc (lines[1]!)
      let paint2Parts := SplitSpacesFunc (lines[2]!)
      let a := ParseIntFunc (boardParts[0]!)
      let b := ParseIntFunc (boardParts[1]!)
      let c := ParseIntFunc (paint1Parts[0]!)
      let d := ParseIntFunc (paint1Parts[1]!)
      let e := ParseIntFunc (paint2Parts[0]!)
      let f := ParseIntFunc (paint2Parts[1]!)
      CanPlaceBothPaintings a b c d e f)) ∧
  (¬ValidInput input → result = "")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
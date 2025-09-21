-- <vc-preamble>
def lengthSqr (p1 p2 : Int × Int) : Int :=
  (p1.1 - p2.1) * (p1.1 - p2.1) + (p1.2 - p2.2) * (p1.2 - p2.2)

def ValidRotationExists (a b c : Int × Int) : Prop :=
  let distABSqr := lengthSqr a b
  let distBCSqr := lengthSqr b c
  let dx1 := c.1 - b.1
  let dy1 := c.2 - b.2
  let dx2 := b.1 - a.1
  let dy2 := b.2 - a.2
  distABSqr = distBCSqr ∧ dx1 * dy2 ≠ dy1 * dx2

def charToDigit (c : Char) : Int :=
  Int.ofNat (c.toNat - '0'.toNat)

def isDigitString (s : String) : Bool :=
  s.all (fun c => '0' ≤ c ∧ c ≤ '9')

def stringToIntHelper (s : String) : Int :=
  s.foldl (fun acc c => acc * 10 + charToDigit c) 0

def stringToInt (s : String) : Int :=
  if s.isEmpty then 0
  else if s = "-" then 0
  else if s.startsWith "-" ∧ s.length > 1 ∧ isDigitString (s.drop 1) then 
    -(stringToIntHelper (s.drop 1))
  else if isDigitString s then stringToIntHelper s
  else 0

def parseInputHelper (input : String) (i : Nat) (result : List Int) (current : String) : List Int :=
  if i ≥ input.length then
    if current.length > 0 then result ++ [stringToInt current]
    else result
  else
    let ch := if h : i < input.length then input.data[i]! else ' '
    if ch = ' ' ∨ ch = '\n' ∨ ch = '\t' then
      if current.length > 0 then
        parseInputHelper input (i + 1) (result ++ [stringToInt current]) ""
      else
        parseInputHelper input (i + 1) result ""
    else if ('0' ≤ ch ∧ ch ≤ '9') ∨ ch = '-' then
      parseInputHelper input (i + 1) result (current ++ ch.toString)
    else
      parseInputHelper input (i + 1) result current

def parseInputFunc (input : String) : List Int :=
  parseInputHelper input 0 [] ""

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
  (result = "Yes" ∨ result = "No" ∨ result = "") ∧
  (let coords := parseInputFunc input
   coords.length ≠ 6 → result = "") ∧
  (let coords := parseInputFunc input
   coords.length = 6 → 
     let a := (coords[0]!, coords[1]!)
     let b := (coords[2]!, coords[3]!)
     let c := (coords[4]!, coords[5]!)
     (ValidRotationExists a b c → result = "Yes") ∧
     (¬ValidRotationExists a b c → result = "No"))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
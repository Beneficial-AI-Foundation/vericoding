-- <vc-preamble>
def Pow10 : Nat → Int
| 0 => 1
| n + 1 => 10 * Pow10 n

partial def ParseInt (s : String) : Int :=
  if s.length = 0 then 0
  else if s.length = 1 then
    if '0' ≤ s.data[0]! ∧ s.data[0]! ≤ '9' then 
      s.data[0]!.toNat - '0'.toNat 
    else 0
  else
    if '0' ≤ s.data[0]! ∧ s.data[0]! ≤ '9' then
      (s.data[0]!.toNat - '0'.toNat) * Pow10 (s.length - 1) + ParseInt (s.drop 1)
    else 0

partial def SplitByNewline (s : String) : List String :=
  if s.length = 0 then []
  else if s.data[0]! = '\n' then [""] ++ SplitByNewline (s.drop 1)
  else 
    let rest := SplitByNewline (s.drop 1)
    if rest.length = 0 then [s]
    else [s.take 1 ++ rest.head!] ++ rest.tail

partial def SplitBySpace (s : String) : List String :=
  if s.length = 0 then []
  else if s.data[0]! = ' ' then [""] ++ SplitBySpace (s.drop 1)
  else 
    let rest := SplitBySpace (s.drop 1)
    if rest.length = 0 then [s]
    else [s.take 1 ++ rest.head!] ++ rest.tail

def IsValidInt (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9'

def IsValidTwoIntLine (s : String) : Prop :=
  let parts := SplitBySpace s
  parts.length ≥ 2 ∧ IsValidInt parts[0]! ∧ IsValidInt parts[1]!

def ValidInputFormat (input : String) : Prop :=
  let lines := SplitByNewline input
  lines.length ≥ 1 ∧ 
  IsValidInt lines[0]! ∧
  let t := ParseInt lines[0]!
  t ≥ 0 ∧ Int.natAbs t + 1 ≤ lines.length ∧
  ∀ i, 1 ≤ i ∧ i ≤ Int.natAbs t → IsValidTwoIntLine lines[i]!

def ValidOutputFormat (output input : String) : Prop :=
  let inputLines := SplitByNewline input
  if inputLines.length = 0 then output = ""
  else
    let t := ParseInt inputLines[0]!
    let outputLines := SplitByNewline output
    outputLines.length = Int.natAbs t ∧
    ∀ i, i < Int.natAbs t → (outputLines[i]! = "YES" ∨ outputLines[i]! = "NO")

def CorrectDivisibilityResults (input output : String) : Prop :=
  let inputLines := SplitByNewline input
  if inputLines.length = 0 then output = ""
  else
    let t := ParseInt inputLines[0]!
    let outputLines := SplitByNewline output
    outputLines.length = Int.natAbs t ∧
    ∀ i, i < Int.natAbs t ∧ i + 1 < inputLines.length → 
      let parts := SplitBySpace inputLines[i + 1]!
      parts.length ≥ 2 →
        let x := ParseInt parts[0]!
        let y := ParseInt parts[1]!
        y ≠ 0 →
          (outputLines[i]! = "YES" ↔ x % y = 0)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInputFormat input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (output : String) (h_precond : solve_precond input) : Prop :=
  (∀ i, i < output.length → output.data[i]! ∈ ['Y', 'E', 'S', 'N', 'O', '\n']) ∧
  ValidOutputFormat output input ∧
  CorrectDivisibilityResults input output

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
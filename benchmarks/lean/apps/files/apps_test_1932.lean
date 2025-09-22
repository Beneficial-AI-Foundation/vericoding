-- <vc-preamble>

def TrimStart (s : String) (i : Nat) : Nat :=
  if i ≥ s.length then i
  else if s.get ⟨i⟩ = ' ' ∨ s.get ⟨i⟩ = '\t' ∨ s.get ⟨i⟩ = '\r' ∨ s.get ⟨i⟩ = '\n' then
    TrimStart s (i + 1)
  else i
termination_by s.length - i

def TrimEnd (s : String) (j : Nat) (start : Nat) : Nat :=
  if j ≤ start then start
  else if s.get ⟨j - 1⟩ = ' ' ∨ s.get ⟨j - 1⟩ = '\t' ∨ s.get ⟨j - 1⟩ = '\r' ∨ s.get ⟨j - 1⟩ = '\n' then
    TrimEnd s (j - 1) start
  else j
termination_by j - start

def TrimFunc (s : String) : String :=
  let start := TrimStart s 0
  let endPos := TrimEnd s s.length start
  if start < endPos then s.extract ⟨start⟩ ⟨endPos⟩ else ""

def StringToIntHelper (s : String) (i : Nat) (acc : Int) : Int :=
  if i ≥ s.length then acc
  else if '0' ≤ s.get ⟨i⟩ ∧ s.get ⟨i⟩ ≤ '9' then
    StringToIntHelper s (i + 1) (acc * 10 + (s.get ⟨i⟩).toNat - '0'.toNat)
  else
    StringToIntHelper s (i + 1) acc
termination_by s.length - i

def StringToIntFunc (s : String) : Int :=
  let trimmed := TrimFunc s
  if trimmed.length = 0 then 0
  else StringToIntHelper trimmed 0 0

def IntToStringHelper (n : Nat) : String :=
  if n = 0 then ""
  else if n < 10 then 
    String.mk [Char.ofNat (n + '0'.toNat)]
  else 
    IntToStringHelper (n / 10) ++ String.mk [Char.ofNat ((n % 10) + '0'.toNat)]
termination_by n

def IntToStringFunc (n : Int) : String :=
  if n ≥ 0 then
    if n = 0 then "0"
    else IntToStringHelper n.natAbs
  else "0"

def SplitLinesHelper (s : String) (start : Nat) (i : Nat) (acc : List String) : List String :=
  if i ≥ s.length then
    if start < s.length then acc ++ [s.extract ⟨start⟩ ⟨s.length⟩]
    else acc
  else if s.get ⟨i⟩ = '\n' then
    let newAcc := if start ≤ i then acc ++ [s.extract ⟨start⟩ ⟨i⟩] else acc
    SplitLinesHelper s (i + 1) (i + 1) newAcc
  else
    SplitLinesHelper s start (i + 1) acc
termination_by s.length - i

def SplitLinesFunc (s : String) : List String :=
  if s.length > 0 then SplitLinesHelper s 0 0 []
  else []

def GetFaces (polyhedron : String) : Int :=
  if polyhedron = "Tetrahedron" then 4
  else if polyhedron = "Cube" then 6
  else if polyhedron = "Octahedron" then 8
  else if polyhedron = "Dodecahedron" then 12
  else if polyhedron = "Icosahedron" then 20
  else 0

def ComputeTotalUpTo (lines : List String) (count : Nat) : Int :=
  if count = 0 then 0
  else if count ≥ lines.length then 0
  else GetFaces (TrimFunc (lines[count - 1]!)) + ComputeTotalUpTo lines (count - 1)
termination_by count

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ 
  let lines := SplitLinesFunc input
  lines.length ≥ 2 ∧ 
  StringToIntFunc (lines[0]!) ≥ 1 ∧
  StringToIntFunc (lines[0]!) ≤ lines.length - 1

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
def solve_postcond (input : String) (result: String) (h_precond : solve_precond input) : Prop :=
  result.length > 0 ∧
  result.get ⟨result.length - 1⟩ = '\n' ∧
  (∃ totalFaces, totalFaces ≥ 0 ∧ result = IntToStringFunc totalFaces ++ "\n") ∧
  (ValidInput input → 
    let lines := SplitLinesFunc input
    let n := StringToIntFunc (lines[0]!)
    let expectedTotal := ComputeTotalUpTo lines n.natAbs
    result = IntToStringFunc expectedTotal ++ "\n")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
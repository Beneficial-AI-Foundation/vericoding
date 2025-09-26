-- <vc-preamble>
-- String processing functions (axiomatized for now)
axiom SplitLines : String → List String
axiom SplitSpaces : String → List String
axiom StringToInt : String → Int
axiom IsValidInteger : String → Bool

noncomputable def ValidFirstLine (line : String) : Prop :=
  let parts := SplitSpaces line
  parts.length = 2 ∧ IsValidInteger (parts[0]!) ∧ IsValidInteger (parts[1]!)

noncomputable def ValidSecondLine (line : String) : Prop :=
  IsValidInteger line

noncomputable def ValidGrasshopperLine (line : String) (n : Int) : Prop :=
  let parts := SplitSpaces line
  parts.length = 2 ∧ IsValidInteger (parts[0]!) ∧ IsValidInteger (parts[1]!) ∧
  StringToInt (parts[0]!) ≥ 0 ∧ StringToInt (parts[0]!) ≤ n ∧
  StringToInt (parts[1]!) ≥ 0 ∧ StringToInt (parts[1]!) ≤ n

noncomputable def ValidGrasshopperLinesSimple (lines : List String) : Prop :=
  lines.length ≥ 3 ∧
  let m := StringToInt (lines[1]!)
  lines.length ≥ 2 + m.natAbs

noncomputable def ValidInput (input : String) : Prop :=
  let lines := SplitLines input
  lines.length ≥ 3 ∧
  ValidFirstLine (lines[0]!) ∧
  ValidSecondLine (lines[1]!) ∧
  ValidGrasshopperLinesSimple lines ∧
  let firstLine := SplitSpaces (lines[0]!)
  let n := StringToInt (firstLine[0]!)
  let d := StringToInt (firstLine[1]!)
  let m := StringToInt (lines[1]!)
  d ≥ 1 ∧ d < n ∧ n ≤ 100 ∧
  m ≥ 1 ∧ m ≤ 100 ∧
  lines.length ≥ 2 + m.natAbs ∧
  ∀ i, 0 ≤ i ∧ i < m → ValidGrasshopperLine (lines[2 + i.natAbs]!) n

noncomputable def GetN (input : String) (h : ValidInput input) : Int :=
  let lines := SplitLines input
  let firstLine := SplitSpaces (lines[0]!)
  StringToInt (firstLine[0]!)

noncomputable def GetD (input : String) (h : ValidInput input) : Int :=
  let lines := SplitLines input
  let firstLine := SplitSpaces (lines[0]!)
  StringToInt (firstLine[1]!)

noncomputable def GetNumberOfGrasshoppers (input : String) (h : ValidInput input) : Int :=
  let lines := SplitLines input
  StringToInt (lines[1]!)

noncomputable def GetGrasshopper (input : String) (i : Int) (h : ValidInput input) 
    (hi : 0 ≤ i ∧ i < GetNumberOfGrasshoppers input h) : Int × Int :=
  let lines := SplitLines input
  let coords := SplitSpaces (lines[2 + i.natAbs]!)
  (StringToInt (coords[0]!), StringToInt (coords[1]!))

def IsInsideCornfield (grasshopper : Int × Int) (n : Int) (d : Int) : Bool :=
  let (x, y) := grasshopper
  (x + y ≥ d && x + y ≤ 2 * n - d && x - y ≥ -d && x - y ≤ d)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (input : String) (h_precond : solve_precond input) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
noncomputable def solve_postcond (input : String) (result : List String) (h_precond : solve_precond input) : Prop :=
  let h_valid : ValidInput input := h_precond.2
  result.length = (GetNumberOfGrasshoppers input h_valid).natAbs ∧
  (∀ i, 0 ≤ i ∧ i < result.length → result[i]! = "YES" ∨ result[i]! = "NO") ∧
  (∀ i, 0 ≤ i ∧ i < result.length → 
    let grasshopper := GetGrasshopper input i h_valid ⟨by sorry, by sorry⟩
    result[i]! = (if IsInsideCornfield grasshopper (GetN input h_valid) (GetD input h_valid) then "YES" else "NO"))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
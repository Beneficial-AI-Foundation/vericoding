-- <vc-preamble>
-- Helper functions for string processing (axiomatized)
axiom SplitLines : String → List String
axiom SplitSpaces : String → List String  
axiom IsValidInteger : String → Bool
axiom ParseInt : String → Int
axiom IntToString : Int → String
axiom JoinLines : List String → String

def ValidInput (input : String) : Prop :=
  let lines := SplitLines input
  lines.length > 0 ∧
  IsValidInteger (lines[0]!) ∧
  let t := ParseInt (lines[0]!)
  t ≥ 0 ∧ Int.natAbs lines.length ≥ Int.natAbs t + 1 ∧
  (∀ i : Nat, 1 ≤ i ∧ i ≤ Int.natAbs t → 
    let line_parts := SplitSpaces (lines[i]!)
    line_parts.length ≥ 4 ∧
    (∀ j : Nat, j < 4 → IsValidInteger (line_parts[j]!)) ∧
    let L := ParseInt (line_parts[0]!)
    let v := ParseInt (line_parts[1]!)
    let l := ParseInt (line_parts[2]!)
    let r := ParseInt (line_parts[3]!)
    L ≥ 1 ∧ v ≥ 1 ∧ l ≥ 1 ∧ r ≥ l ∧ r ≤ L)

def ValidOutput (output : String) : Prop :=
  ∀ c, c ∈ output.data → (c ≥ '0' ∧ c ≤ '9') ∨ c = '-' ∨ c = '\n'

def OutputMatchesAlgorithm (output : String) (input : String) : Prop :=
  let lines := SplitLines input
  let t := ParseInt (lines[0]!)
  t ≥ 0 ∧
  let expectedLines := List.range (Int.natAbs t) |>.map (fun i =>
    if i + 1 < lines.length ∧ (SplitSpaces (lines[i + 1]!)).length ≥ 4 then
      let parts := SplitSpaces (lines[i + 1]!)
      let L := ParseInt (parts[0]!)
      let v := ParseInt (parts[1]!)
      let l := ParseInt (parts[2]!)
      let r := ParseInt (parts[3]!)
      let totalLanterns := L / v
      let blockedLanterns := r / v - (l - 1) / v
      let visibleLanterns := totalLanterns - blockedLanterns
      IntToString visibleLanterns
    else
      "0")
  output = JoinLines expectedLines

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInput input
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
  ValidOutput result ∧ OutputMatchesAlgorithm result input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
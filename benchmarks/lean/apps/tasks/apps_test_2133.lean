-- <vc-preamble>
def SplitLines (_ : String) : List String := []
def ParseInt (_ : String) : Int := 0
def ParseIntSeq (_ : String) : List Int := []
def TrimWhitespace (s : String) : String := s
def TreeDiameter (_ : List (List Int)) : Int := 0
def BuildSameColorComponents (_ : List Int) (_ : List (Int × Int)) : List (List Int) := []
def BuildComponentGraph (_ : List (List Int)) (_ : List Int) (_ : List (Int × Int)) : List (List Int) := []

def ValidColorLine (line : String) (n : Int) : Prop :=
  let colors := ParseIntSeq line
  colors.length = n ∧
  ∀ i, 0 ≤ i ∧ i < colors.length → colors[i]! = 0 ∨ colors[i]! = 1

def ValidEdgeLines (lines : List String) (n : Int) : Prop :=
  lines.length = n - 1 ∧
  ∀ i, 0 ≤ i ∧ i < lines.length → 
    let edge := ParseIntSeq lines[i]!
    edge.length = 2 ∧ 
    1 ≤ edge[0]! ∧ edge[0]! ≤ n ∧ 
    1 ≤ edge[1]! ∧ edge[1]! ≤ n ∧ 
    edge[0]! ≠ edge[1]!

def NoDuplicateEdges (edges : List (Int × Int)) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < edges.length → 
    edges[i]! ≠ edges[j]! ∧ 
    (edges[i]!.1, edges[i]!.2) ≠ (edges[j]!.2, edges[j]!.1)

def IsConnected (_ : Int) (_ : List (Int × Int)) : Prop := True

def IsValidTree (n : Int) (edges : List (Int × Int)) : Prop :=
  n ≥ 1 ∧
  edges.length = n - 1 ∧
  IsConnected n edges ∧
  (∀ e, e ∈ edges → 1 ≤ e.1 ∧ e.1 ≤ n ∧ 1 ≤ e.2 ∧ e.2 ≤ n ∧ e.1 ≠ e.2) ∧
  NoDuplicateEdges edges

def ValidTreeInput (input : String) : Prop :=
  let lines := SplitLines input
  lines.length ≥ 2 ∧
  let n := ParseInt lines[0]!
  n ≥ 1 ∧ n ≤ 200000 ∧
  lines.length = n + 1 ∧
  ValidColorLine lines[1]! n ∧
  ValidEdgeLines (lines.drop 2) n ∧
  let edges := (List.range (lines.length - 2)).map (fun i => 
    let edge := ParseIntSeq lines[i + 2]!
    (edge[0]!, edge[1]!))
  IsValidTree n edges

def ValidIntegerOutput (output : String) : Prop :=
  let trimmed := TrimWhitespace output
  trimmed.length > 0 ∧
  ∀ c, c ∈ trimmed.toList → '0' ≤ c ∧ c ≤ '9'

def AllSameColor (colors : List Int) : Bool :=
  if colors.length > 0 then 
    colors.all (· = colors[0]!)
  else false

def ParseInput (input : String) (_ : ValidTreeInput input) : (Int × List Int × List (Int × Int)) :=
  let lines := SplitLines input
  let n := ParseInt lines[0]!
  let colors := ParseIntSeq lines[1]!
  let edges := (List.range (lines.length - 2)).map (fun i => 
    let edge := ParseIntSeq lines[i + 2]!
    (edge[0]!, edge[1]!))
  (n, colors, edges)

def ParseOutput (output : String) : Int :=
  ParseInt (TrimWhitespace output)

def ComputeMinPaintOps (n : Int) (colors : List Int) (edges : List (Int × Int)) : Int :=
  if n ≥ 1 ∧ colors.length = n ∧ edges.length = n - 1 then
    if AllSameColor colors then 0
    else
      let components := BuildSameColorComponents colors edges
      let componentGraph := BuildComponentGraph components colors edges
      (TreeDiameter componentGraph + 1) / 2
  else 0

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ ValidTreeInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (output : String) (h_precond : solve_precond stdin_input) : Prop :=
  output.length > 0 ∧
  ValidIntegerOutput output ∧
  let result := ParseOutput output
  result ≥ 0 ∧
  let (n, colors, edges) := ParseInput stdin_input h_precond.2
  (n ≥ 1 → result ≤ n) ∧
  (AllSameColor colors → ParseOutput output = 0) ∧
  (n = 1 → ParseOutput output = 0) ∧
  IsValidTree n edges ∧ n ≥ 1 ∧
  result = ComputeMinPaintOps n colors edges

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>
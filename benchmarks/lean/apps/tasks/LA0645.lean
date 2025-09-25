-- <vc-preamble>
structure Checkpoint where
  t : Int
  x : Int
  y : Int

-- Helper functions (axiomatized for this translation)
axiom SplitLines : String → List String
axiom IsValidInteger : String → Bool
axiom ParseInt : String → Int
axiom IsValidCheckpointLine : String → Bool
axiom ParseCheckpoints : List String → List Checkpoint

def ValidInputFormat (input : String) : Prop :=
  let lines := SplitLines input
  lines.length > 0 ∧ IsValidInteger (lines.head!) ∧
  (let n := ParseInt (lines.head!)
   n ≥ 0 ∧ n + 1 = lines.length ∧
   (∀ i, 1 ≤ i ∧ i < lines.length → IsValidCheckpointLine (lines.get! i)))

def CheckpointsFeasible (checkpoints : List Checkpoint) (currentT : Int) (currentX : Int) (currentY : Int) : Prop :=
  match checkpoints with
  | [] => True
  | cp :: rest =>
      let dt := cp.t - currentT
      let dx := if currentX ≥ cp.x then currentX - cp.x else cp.x - currentX
      let dy := if currentY ≥ cp.y then currentY - cp.y else cp.y - currentY
      let dis := dx + dy
      if dt < dis then False
      else if (dt - dis) % 2 ≠ 0 then False
      else CheckpointsFeasible rest cp.t cp.x cp.y

def CanVisitAllCheckpoints (input : String) : Prop :=
  let lines := SplitLines input
  let n := ParseInt (lines.head!)
  if n = 0 then True
  else
    let checkpoints := ParseCheckpoints (lines.tail)
    checkpoints.length = n ∧
    CheckpointsFeasible checkpoints 0 0 0

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ ValidInputFormat stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  (result = "Yes\n" ∨ result = "No\n") ∧
  (result = "Yes\n" ↔ CanVisitAllCheckpoints stdin_input)

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>
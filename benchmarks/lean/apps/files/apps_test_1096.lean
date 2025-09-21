-- <vc-preamble>
def getChar (s : String) (i : Nat) : Char :=
  if h : i < s.length then s.get (String.Pos.mk i) else default

def ValidInput (position : String) : Prop :=
  position.length = 2 ∧ 
  'a' ≤ getChar position 0 ∧ getChar position 0 ≤ 'h' ∧
  '1' ≤ getChar position 1 ∧ getChar position 1 ≤ '8'

def IsCorner (position : String) : Prop :=
  ValidInput position ∧
  (getChar position 0 = 'a' ∨ getChar position 0 = 'h') ∧ 
  (getChar position 1 = '1' ∨ getChar position 1 = '8')

def IsEdge (position : String) : Prop :=
  ValidInput position ∧
  (getChar position 0 = 'a' ∨ getChar position 0 = 'h' ∨ 
   getChar position 1 = '1' ∨ getChar position 1 = '8') ∧ 
  ¬IsCorner position

def IsInterior (position : String) : Prop :=
  ValidInput position ∧ ¬IsCorner position ∧ ¬IsEdge position

instance decValidInput (position : String) : Decidable (ValidInput position) := by
  unfold ValidInput getChar
  infer_instance

instance decIsCorner (position : String) : Decidable (IsCorner position) := by
  unfold IsCorner
  infer_instance

instance decIsEdge (position : String) : Decidable (IsEdge position) := by
  unfold IsEdge
  infer_instance

instance decIsInterior (position : String) : Decidable (IsInterior position) := by
  unfold IsInterior
  infer_instance

def ValidMoves (position : String) : Int :=
  if IsCorner position then 3
  else if IsEdge position then 5
  else 8

@[reducible, simp]
def solve_precond (position : String) : Prop :=
  ValidInput position
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (position : String) (_ : solve_precond position) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (position : String) (moves : Int) (h_precond : solve_precond position) : Prop :=
  moves = ValidMoves position ∧
  (IsCorner position → moves = 3) ∧
  (IsEdge position → moves = 5) ∧
  (IsInterior position → moves = 8) ∧
  (moves = 3 ∨ moves = 5 ∨ moves = 8)

theorem solve_spec_satisfied (position : String) (h_precond : solve_precond position) :
    solve_postcond position (solve position h_precond) h_precond := by
  sorry
-- </vc-theorems>
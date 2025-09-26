import Mathlib
-- <vc-preamble>
def ValidPosition (r c : Int) : Prop :=
  1 ≤ r ∧ r ≤ 8 ∧ 1 ≤ c ∧ c ≤ 8

def RookMoves (r1 c1 r2 c2 : Int) : Int :=
  if r1 = r2 ∧ c1 = c2 then 0
  else if r1 = r2 ∨ c1 = c2 then 1
  else 2

def BishopMoves (r1 c1 r2 c2 : Int) : Int :=
  if r1 = r2 ∧ c1 = c2 then 0
  else 
    let row_diff := if r1 ≥ r2 then r1 - r2 else r2 - r1
    let col_diff := if c1 ≥ c2 then c1 - c2 else c2 - c1
    if row_diff = col_diff then 1
    else if (r1 + c1) % 2 = (r2 + c2) % 2 then 2
    else 0

def KingMoves (r1 c1 r2 c2 : Int) : Int :=
  let row_diff := if r1 ≥ r2 then r1 - r2 else r2 - r1
  let col_diff := if c1 ≥ c2 then c1 - c2 else c2 - c1
  if row_diff ≥ col_diff then row_diff else col_diff

def ValidResult (result : List Int) (r1 c1 r2 c2 : Int) : Prop :=
  result.length = 3 ∧
  result[0]! = RookMoves r1 c1 r2 c2 ∧
  result[1]! = BishopMoves r1 c1 r2 c2 ∧
  result[2]! = KingMoves r1 c1 r2 c2

@[reducible, simp]
def solve_precond (r1 c1 r2 c2 : Int) : Prop :=
  ValidPosition r1 c1 ∧ ValidPosition r2 c2
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def solve (r1 c1 r2 c2 : Int) (h_precond : solve_precond r1 c1 r2 c2) : List Int :=
  [RookMoves r1 c1 r2 c2, BishopMoves r1 c1 r2 c2, KingMoves r1 c1 r2 c2]
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (r1 c1 r2 c2 : Int) (result: List Int) (h_precond : solve_precond r1 c1 r2 c2) : Prop :=
  ValidResult result r1 c1 r2 c2

theorem solve_spec_satisfied (r1 c1 r2 c2 : Int) (h_precond : solve_precond r1 c1 r2 c2) :
    solve_postcond r1 c1 r2 c2 (solve r1 c1 r2 c2 h_precond) h_precond := by
  simp [solve_postcond, ValidResult, solve]
-- </vc-theorems>

-- <vc-preamble>
def ValidInput (n: Int) (directions: String) (positions: List Int) : Prop :=
  n ≥ 1 ∧
  directions.length = n.natAbs ∧
  positions.length = n.natAbs ∧
  (∀ i : Nat, i < n.natAbs → directions.data[i]! = 'R' ∨ directions.data[i]! = 'L') ∧
  (∀ i : Nat, i < n.natAbs → positions[i]! % 2 = 0 ∧ positions[i]! ≥ 0) ∧
  (∀ i j : Nat, i < j ∧ j < n.natAbs → positions[i]! < positions[j]!)

def HasCollision (directions: String) (positions: List Int) : Prop :=
  directions.length = positions.length →
  ∃ i : Nat, i < directions.length - 1 ∧ directions.data[i]! = 'R' ∧ directions.data[i+1]! = 'L'

def CollisionTime (i: Nat) (positions: List Int) : Int :=
  if i < positions.length - 1 then
    (positions[i+1]! - positions[i]!) / 2
  else
    0

def IsMinimalCollisionTime (result: Int) (directions: String) (positions: List Int) : Prop :=
  directions.length = positions.length →
  (∀ i : Nat, i < directions.length - 1 ∧ directions.data[i]! = 'R' ∧ directions.data[i+1]! = 'L' → 
      CollisionTime i positions ≥ result) ∧
  (∃ i : Nat, i < directions.length - 1 ∧ directions.data[i]! = 'R' ∧ directions.data[i+1]! = 'L' ∧ 
      CollisionTime i positions = result)

@[reducible, simp]
def solve_precond (n: Int) (directions: String) (positions: List Int) : Prop :=
  ValidInput n directions positions
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n: Int) (directions: String) (positions: List Int) (h_precond: solve_precond n directions positions) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n: Int) (directions: String) (positions: List Int) (result: Int) (h_precond: solve_precond n directions positions) : Prop :=
  (result = -1 ∨ result ≥ 0) ∧
  (result ≠ -1 → HasCollision directions positions) ∧
  (result = -1 → ¬HasCollision directions positions) ∧
  (result ≠ -1 → IsMinimalCollisionTime result directions positions)

theorem solve_spec_satisfied (n: Int) (directions: String) (positions: List Int) (h_precond: solve_precond n directions positions) :
    solve_postcond n directions positions (solve n directions positions h_precond) h_precond := by
  sorry
-- </vc-theorems>
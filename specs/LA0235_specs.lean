-- <vc-preamble>
def isValidPlacement (rooms: String) (k: Int) (placement: List Int) : Prop :=
  placement.length = k + 1 ∧
  (∀ i, 0 ≤ i ∧ i < placement.length → 0 ≤ placement[i]! ∧ placement[i]! < rooms.length) ∧
  (∀ i, 0 ≤ i ∧ i < placement.length → rooms.data[placement[i]!.natAbs]! = '0') ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < placement.length → placement[i]! ≠ placement[j]!) ∧
  (∀ i, 0 ≤ i ∧ i < placement.length - 1 → placement[i]! < placement[i+1]!)

def optimalMaxDistance (placement: List Int) : Int := 0

@[reducible, simp]
def solve_precond (n k : Int) (rooms : String) : Prop :=
  n > 0 ∧
  k > 0 ∧
  k < n ∧
  rooms.length = n ∧
  (∀ i, 0 ≤ i ∧ i < n → rooms.data[i.natAbs]! = '0' ∨ rooms.data[i.natAbs]! = '1') ∧
  (rooms.data.filter (· = '0')).length ≥ (k + 1).natAbs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (rooms : String) (_ : solve_precond n k rooms) : Int :=
  0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (rooms : String) (result : Int) (_ : solve_precond n k rooms) : Prop :=
  result ≥ 0 ∧
  ∃ placement, isValidPlacement rooms k placement ∧ optimalMaxDistance placement = result

theorem solve_spec_satisfied (n k : Int) (rooms : String) (h_precond : solve_precond n k rooms) :
    solve_postcond n k rooms (solve n k rooms h_precond) h_precond := by
  sorry
-- </vc-theorems>
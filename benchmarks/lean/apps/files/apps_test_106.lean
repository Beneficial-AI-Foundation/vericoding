-- <vc-preamble>
def ValidInput (n m k a b : Int) : Prop :=
  n > 0 ∧ m > 0 ∧ k > 0 ∧ 1 ≤ a ∧ a ≤ n * m * k ∧ 1 ≤ b ∧ b ≤ n * m * k ∧ a ≠ b

def GetEntrance (apt m k : Int) : Int :=
  (apt - 1) / (m * k)

def GetFloor (apt m k : Int) : Int :=
  ((apt - 1) - GetEntrance apt m k * m * k) / k

def MinTravelTime (floors : Int) : Int :=
  let stair_time := 5 * floors
  let elevator_time := 10 + floors
  if stair_time < elevator_time then stair_time else elevator_time

def MinEntranceDistance (entrance_a entrance_b n : Int) : Int :=
  let clockwise := (entrance_b - entrance_a + n) % n
  let counterclockwise := (entrance_a - entrance_b + n) % n
  if clockwise ≤ counterclockwise then clockwise else counterclockwise

@[reducible, simp]
def solve_precond (n m k a b : Int) : Prop :=
  ValidInput n m k a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m k a b : Int) (h_precond : solve_precond n m k a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m k a b : Int) (result: Int) (h_precond : solve_precond n m k a b) : Prop :=
  result ≥ 0 ∧
  (GetEntrance a m k = GetEntrance b m k → 
    result = MinTravelTime (if GetFloor a m k ≥ GetFloor b m k 
                           then GetFloor a m k - GetFloor b m k 
                           else GetFloor b m k - GetFloor a m k)) ∧
  (GetEntrance a m k ≠ GetEntrance b m k →
    result = MinTravelTime (GetFloor a m k) + 
              15 * MinEntranceDistance (GetEntrance a m k) (GetEntrance b m k) n + 
              MinTravelTime (GetFloor b m k))

theorem solve_spec_satisfied (n m k a b : Int) (h_precond : solve_precond n m k a b) :
    solve_postcond n m k a b (solve n m k a b h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- <vc-preamble>
def ValidInput (n : Int) (t : Int) (routes : List (Int × Int)) : Prop :=
  n > 0 ∧ routes.length = Int.natAbs n ∧ 
  ∀ i, 0 ≤ i ∧ i < n → (routes[Int.natAbs i]!).2 > 0

def getNextArrivalTime (firstTime : Int) (interval : Int) (targetTime : Int) : Int :=
  if firstTime ≥ targetTime then firstTime
  else firstTime + ((targetTime - firstTime + interval - 1) / interval) * interval

def IsOptimalRoute (routes : List (Int × Int)) (t : Int) (routeIndex : Int) : Prop :=
  0 ≤ routeIndex ∧ Int.natAbs routeIndex < routes.length ∧
  (∀ i, 0 ≤ i ∧ Int.natAbs i < routes.length → (routes[Int.natAbs i]!).2 > 0) →
  ∀ i, 0 ≤ i ∧ Int.natAbs i < routes.length → 
    getNextArrivalTime (routes[Int.natAbs routeIndex]!).1 (routes[Int.natAbs routeIndex]!).2 t ≤ 
    getNextArrivalTime (routes[Int.natAbs i]!).1 (routes[Int.natAbs i]!).2 t

@[reducible, simp]
def solve_precond (n : Int) (t : Int) (routes : List (Int × Int)) : Prop :=
  ValidInput n t routes
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (t : Int) (routes : List (Int × Int)) (h_precond : solve_precond n t routes) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (t : Int) (routes : List (Int × Int)) (result : Int) (h_precond : solve_precond n t routes) : Prop :=
  1 ≤ result ∧ result ≤ n ∧ IsOptimalRoute routes t (result - 1)

theorem solve_spec_satisfied (n : Int) (t : Int) (routes : List (Int × Int)) (h_precond : solve_precond n t routes) :
    solve_postcond n t routes (solve n t routes h_precond) h_precond := by
  sorry
-- </vc-theorems>
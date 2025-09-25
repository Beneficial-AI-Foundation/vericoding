-- <vc-preamble>
def ValidInput (cities : List Int) : Prop :=
  cities.length ≥ 2 ∧
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < cities.length → cities[i]! < cities[j]!

def MinDistance (cities : List Int) (i : Nat) : Int :=
  if i = 0 then
    cities[1]! - cities[0]!
  else if i = cities.length - 1 then
    cities[i]! - cities[i-1]!
  else
    let left_dist := cities[i]! - cities[i-1]!
    let right_dist := cities[i+1]! - cities[i]!
    if left_dist ≤ right_dist then left_dist else right_dist

def MaxDistance (cities : List Int) (i : Nat) : Int :=
  if i = 0 then
    cities[cities.length-1]! - cities[0]!
  else if i = cities.length - 1 then
    cities[i]! - cities[0]!
  else
    let dist_to_first := cities[i]! - cities[0]!
    let dist_to_last := cities[cities.length-1]! - cities[i]!
    if dist_to_first ≥ dist_to_last then dist_to_first else dist_to_last

def ValidOutput (cities : List Int) (min_distances : List Int) (max_distances : List Int) : Prop :=
  ValidInput cities ∧
  min_distances.length = cities.length ∧
  max_distances.length = cities.length ∧
  ∀ i, 0 ≤ i ∧ i < cities.length →
    min_distances[i]! = MinDistance cities i ∧
    max_distances[i]! = MaxDistance cities i ∧
    min_distances[i]! > 0 ∧
    max_distances[i]! > 0

@[reducible, simp]
def solve_precond (cities : List Int) : Prop :=
  ValidInput cities
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (cities : List Int) (h_precond : solve_precond cities) : List Int × List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (cities : List Int) (result: List Int × List Int) (h_precond : solve_precond cities) : Prop :=
  ValidOutput cities result.1 result.2

theorem solve_spec_satisfied (cities : List Int) (h_precond : solve_precond cities) :
    solve_postcond cities (solve cities h_precond) h_precond := by
  sorry
-- </vc-theorems>
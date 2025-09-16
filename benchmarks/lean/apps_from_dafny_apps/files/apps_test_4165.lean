-- <vc-preamble>
-- <vc-preamble>
def ValidInput (sides : List Int) : Prop :=
  sides.length ≥ 3 ∧ ∀ i, 0 ≤ i ∧ i < sides.length → sides[i]! > 0

def filter (s : List Int) (pred : Int → Bool) : List Int :=
  s.filter pred

def quicksort (s : List Int) : List Int :=
  sorry

def sumExceptLast (s : List Int) : Int :=
  if s.length ≤ 1 then 0
  else s.take (s.length - 1) |>.sum

def canFormPolygon (sides : List Int) : Bool :=
  let sortedSides := quicksort sides
  let longest := sortedSides[sortedSides.length - 1]!
  let sumOfOthers := sumExceptLast sortedSides
  sumOfOthers > longest

@[reducible, simp]
def solve_precond (sides : List Int) : Prop :=
  ValidInput sides
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (sides : List Int) (h_precond : solve_precond sides) : String :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (sides : List Int) (result : String) (h_precond : solve_precond sides) : Prop :=
  (result = "Yes" ∨ result = "No") ∧ (result = "Yes" ↔ canFormPolygon sides)

theorem solve_spec_satisfied (sides : List Int) (h_precond : solve_precond sides) :
    solve_postcond sides (solve sides h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>

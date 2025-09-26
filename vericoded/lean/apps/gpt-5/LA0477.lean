import Mathlib
-- <vc-preamble>
def ValidInput (sides : List Int) : Prop :=
  sides.length ≥ 3 ∧ ∀ i, 0 ≤ i ∧ i < sides.length → sides[i]! > 0

def filter (s : List Int) (pred : Int → Bool) : List Int :=
  s.filter pred

def sumExceptLast (s : List Int) : Int :=
  if s.length ≤ 1 then 0
  else s.dropLast.sum

def quicksort (s : List Int) : List Int :=
  s.mergeSort (· ≤ ·)

def canFormPolygon (sides : List Int) : Bool :=
  let sortedSides := quicksort sides
  let longest := sortedSides[sortedSides.length - 1]!
  let sumOfOthers := sumExceptLast sortedSides
  sumOfOthers > longest

@[reducible, simp]
def solve_precond (sides : List Int) : Prop :=
  ValidInput sides
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma yes_eq_no_iff_false : ("Yes" = "No" ↔ False) := by
  constructor
  · intro h; exact (by decide : "Yes" ≠ "No") h
  · intro h; exact h.elim

-- LLM HELPER
@[simp] lemma no_eq_yes_iff_false : ("No" = "Yes" ↔ False) := by
  constructor
  · intro h; exact (by decide : "No" ≠ "Yes") h
  · intro h; exact h.elim
-- </vc-helpers>

-- <vc-definitions>
def solve (sides : List Int) (h_precond : solve_precond sides) : String :=
  if canFormPolygon sides then "Yes" else "No"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (sides : List Int) (result : String) (h_precond : solve_precond sides) : Prop :=
  (result = "Yes" ∨ result = "No") ∧ (result = "Yes" ↔ canFormPolygon sides)

theorem solve_spec_satisfied (sides : List Int) (h_precond : solve_precond sides) :
    solve_postcond sides (solve sides h_precond) h_precond := by
  by_cases hcf : canFormPolygon sides
  · simp [solve_postcond, solve, hcf]
  · simp [solve_postcond, solve, hcf]
-- </vc-theorems>

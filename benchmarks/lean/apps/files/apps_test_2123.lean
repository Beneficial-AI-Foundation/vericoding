-- <vc-preamble>
def ValidInput (n : Int) (heights : List Int) : Prop :=
  n > 0 ∧ heights.length = n.natAbs

def MaxInSeq (s : List Int) : Int :=
  if h : s.length > 0 then
    s.foldl max (s.get ⟨0, h⟩)
  else
    0

def ValidResult (n : Int) (heights : List Int) (result : Int) : Prop :=
  ValidInput n heights →
  result = MaxInSeq heights ∧
  (∀ i : Fin heights.length, heights.get i ≤ result) ∧
  (∃ i : Fin heights.length, heights.get i = result)

@[reducible, simp]
def solve_precond (n : Int) (heights : List Int) : Prop :=
  ValidInput n heights
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (heights : List Int) (h_precond : solve_precond n heights) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (heights : List Int) (result : Int) (h_precond : solve_precond n heights) : Prop :=
  ValidResult n heights result

theorem solve_spec_satisfied (n : Int) (heights : List Int) (h_precond : solve_precond n heights) :
    solve_postcond n heights (solve n heights h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- <vc-preamble>
def ValidInput (n : Int) (colors : List Char) : Prop :=
  1 ≤ n ∧ n ≤ 100 ∧
  colors.length = n ∧
  (∀ c ∈ colors, c ∈ ['P', 'W', 'G', 'Y']) ∧
  'P' ∈ colors ∧ 'W' ∈ colors ∧ 'G' ∈ colors

def DistinctColors (colors : List Char) : List Char :=
  colors.eraseDups

def SolutionString (distinctCount : Int) : String :=
  if distinctCount = 3 then "Three" else "Four"

@[reducible, simp]
def solve_precond (n : Int) (colors : List Char) : Prop :=
  ValidInput n colors
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (colors : List Char) (h_precond : solve_precond n colors) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (colors : List Char) (result : String) (h_precond : solve_precond n colors) : Prop :=
  let distinctColors := DistinctColors colors
  (distinctColors.length = 3 ∨ distinctColors.length = 4) ∧
  (distinctColors.length = 3 → result = "Three") ∧
  (distinctColors.length = 4 → result = "Four") ∧
  (result = "Three" ∨ result = "Four")

theorem solve_spec_satisfied (n : Int) (colors : List Char) (h_precond : solve_precond n colors) :
    solve_postcond n colors (solve n colors h_precond) h_precond := by
  sorry
-- </vc-theorems>
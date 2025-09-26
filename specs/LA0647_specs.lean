-- <vc-preamble>
def ValidInput (a b c d e f : Int) : Prop :=
  1 ≤ a ∧ a < b ∧ b ≤ 30 ∧
  1 ≤ c ∧ c < d ∧ d ≤ 30 ∧
  1 ≤ e ∧ e ≤ 100 ∧
  100 * a ≤ f ∧ f ≤ 3000

def ValidSolution (a b c d e f total_mass sugar_mass : Int) : Prop :=
  total_mass > 0 ∧ sugar_mass ≥ 0 ∧
  total_mass ≤ f ∧
  sugar_mass ≤ total_mass

def Density (total_mass sugar_mass : Int) : Int :=
  if total_mass > 0 then (100 * sugar_mass) / total_mass else 0

@[reducible, simp]
def solve_precond (a b c d e f : Int) : Prop :=
  ValidInput a b c d e f
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c d e f : Int) (h_precond : solve_precond a b c d e f) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c d e f : Int) (result: Int × Int) (h_precond : solve_precond a b c d e f) : Prop :=
  let total_mass := result.1
  let sugar_mass := result.2
  ValidSolution a b c d e f total_mass sugar_mass ∧
  total_mass ≥ 0 ∧ sugar_mass ≥ 0 ∧
  total_mass ≤ f ∧
  sugar_mass ≤ total_mass ∧
  (∃ water_units, water_units > 0 ∧ total_mass = water_units * 100 + sugar_mass) ∧
  (∃ water_units, water_units > 0 ∧ sugar_mass ≤ water_units * e) ∧
  (∃ i1 j1 i2 j2, 
      i1 ≥ 0 ∧ j1 ≥ 0 ∧ i2 ≥ 0 ∧ j2 ≥ 0 ∧
      i1 ≤ 30 / a ∧ j1 ≤ 30 / b ∧
      i2 ≤ 3000 / c ∧ j2 ≤ 3000 / d ∧
      total_mass = (a * i1 + b * j1) * 100 + (c * i2 + d * j2) ∧
      sugar_mass = c * i2 + d * j2 ∧
      a * i1 + b * j1 > 0) ∧
  total_mass > 0

theorem solve_spec_satisfied (a b c d e f : Int) (h_precond : solve_precond a b c d e f) :
    solve_postcond a b c d e f (solve a b c d e f h_precond) h_precond := by
  sorry
-- </vc-theorems>
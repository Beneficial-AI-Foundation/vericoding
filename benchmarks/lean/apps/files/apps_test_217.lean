-- <vc-preamble>
def ValidInput (a b f k : Int) : Prop :=
  a > 0 ∧ b > 0 ∧ f > 0 ∧ k > 0 ∧ f < a

def ImpossibleConditions (a b f k : Int) : Prop :=
  b < f ∨
  b < a - f ∨
  (k > 1 ∧ b < 2 * a - f) ∨
  (k = 1 ∧ b < a ∧ b < f)

def FeasibilityConditions (a b f k : Int) : Prop :=
  b ≥ f ∧
  b ≥ a - f ∧
  (k ≤ 1 ∨ b ≥ 2 * a - f) ∧
  (k = 1 → (b ≥ a ∨ b ≥ f))

def SingleJourneyResult (a b f k result : Int) : Prop :=
  k = 1 ∧ result ≥ 0 → (
    (b ≥ a ∧ result = 0) ∨
    (b < a ∧ b ≥ f ∧ result = 1)
  )

def MultiJourneyFeasibility (a b f k result : Int) : Prop :=
  k > 1 ∧ result ≥ 0 → (
    b ≥ f ∧ b ≥ a - f ∧ b ≥ 2 * a - f
  )

@[reducible, simp]
def solve_precond (a b f k : Int) : Prop :=
  ValidInput a b f k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b f k : Int) (h_precond : solve_precond a b f k) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b f k : Int) (result : Int) (h_precond : solve_precond a b f k) : Prop :=
  result ≥ -1 ∧
  (result = -1 ↔ ImpossibleConditions a b f k) ∧
  (result ≥ 0 → result ≤ k) ∧
  (result ≥ 0 → FeasibilityConditions a b f k) ∧
  SingleJourneyResult a b f k result ∧
  MultiJourneyFeasibility a b f k result

theorem solve_spec_satisfied (a b f k : Int) (h_precond : solve_precond a b f k) :
    solve_postcond a b f k (solve a b f k h_precond) h_precond := by
  sorry
-- </vc-theorems>
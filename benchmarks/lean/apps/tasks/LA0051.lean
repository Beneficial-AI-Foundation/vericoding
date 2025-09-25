-- <vc-preamble>
def ValidInput (C Hr Hb Wr Wb : Int) : Prop :=
  C ≥ 0 ∧ Hr > 0 ∧ Hb > 0 ∧ Wr > 0 ∧ Wb > 0

def ValidCandyCombination (redCount blueCount C Wr Wb : Int) : Prop :=
  redCount ≥ 0 ∧ blueCount ≥ 0 ∧ redCount * Wr + blueCount * Wb ≤ C

def Joy (redCount blueCount Hr Hb : Int) : Int :=
  redCount * Hr + blueCount * Hb

@[reducible, simp]
def solve_precond (C Hr Hb Wr Wb : Int) : Prop :=
  ValidInput C Hr Hb Wr Wb
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (C Hr Hb Wr Wb : Int) (h_precond : solve_precond C Hr Hb Wr Wb) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (C Hr Hb Wr Wb : Int) (result : Int) (h_precond : solve_precond C Hr Hb Wr Wb) : Prop :=
  result ≥ 0 ∧
  (∃ redCount blueCount, ValidCandyCombination redCount blueCount C Wr Wb ∧
    result = Joy redCount blueCount Hr Hb) ∧
  (∀ redCount blueCount, ValidCandyCombination redCount blueCount C Wr Wb →
    Joy redCount blueCount Hr Hb ≤ result)

theorem solve_spec_satisfied (C Hr Hb Wr Wb : Int) (h_precond : solve_precond C Hr Hb Wr Wb) :
    solve_postcond C Hr Hb Wr Wb (solve C Hr Hb Wr Wb h_precond) h_precond := by
  sorry
-- </vc-theorems>
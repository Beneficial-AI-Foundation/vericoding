import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  1 ≤ n ∧ n ≤ 10000

def ValidChange (change : Int) : Prop :=
  0 ≤ change ∧ change ≤ 999

def CorrectChange (n : Int) (h : ValidInput n) : Int :=
  (1000 - n % 1000) % 1000

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper lemmas for modular arithmetic
lemma mod_lt_of_pos (a : Int) (b : Int) (hb : 0 < b) : 0 ≤ a % b ∧ a % b < b := by
  constructor
  · exact Int.emod_nonneg a (ne_of_gt hb)
  · exact Int.emod_lt_of_pos a hb

-- LLM HELPER: Bounds for CorrectChange
lemma correct_change_bounds (n : Int) (h : ValidInput n) : ValidChange (CorrectChange n h) := by
  unfold ValidChange CorrectChange
  constructor
  · -- Prove 0 ≤ (1000 - n % 1000) % 1000
    exact Int.emod_nonneg _ (by norm_num)
  · -- Prove (1000 - n % 1000) % 1000 ≤ 999
    have h1000 : (0 : Int) < 1000 := by norm_num
    have hmod := Int.emod_lt_of_pos (1000 - n % 1000) h1000
    linarith
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  CorrectChange n h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (change : Int) (h_precond : solve_precond n) : Prop :=
  ValidChange change ∧ change = CorrectChange n h_precond

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  unfold solve_postcond
  constructor
  · -- Prove ValidChange (solve n h_precond)
    exact correct_change_bounds n h_precond
  · -- Prove solve n h_precond = CorrectChange n h_precond
    rfl
-- </vc-theorems>

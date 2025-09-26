import Mathlib
-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  a ≥ 1 ∧ b ≥ 1

def MaxDifferentDays (a b : Int) : Int :=
  if a < b then a else b

def RemainingAfterDifferent (a b : Int) : Int :=
  if a > b then a - MaxDifferentDays a b else b - MaxDifferentDays a b

def SameDays (a b : Int) : Int :=
  RemainingAfterDifferent a b / 2

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma max_different_days_le (a b : Int) (h : ValidInput a b) :
    MaxDifferentDays a b ≤ a ∧ MaxDifferentDays a b ≤ b := by
  unfold MaxDifferentDays ValidInput at *
  split_ifs with h_cmp
  · exact ⟨le_refl a, le_of_lt h_cmp⟩
  · exact ⟨le_of_not_gt h_cmp, le_refl b⟩

-- LLM HELPER  
lemma max_different_days_nonneg (a b : Int) (h : ValidInput a b) :
    MaxDifferentDays a b ≥ 0 := by
  unfold MaxDifferentDays ValidInput at *
  split_ifs
  · exact le_trans (Int.one_pos.le) h.1
  · exact le_trans (Int.one_pos.le) h.2

-- LLM HELPER
lemma same_days_nonneg (a b : Int) (h : ValidInput a b) :
    SameDays a b ≥ 0 := by
  unfold SameDays RemainingAfterDifferent MaxDifferentDays ValidInput at *
  apply Int.ediv_nonneg
  · split_ifs with h1 h2
    · -- a > b and a < b: contradiction
      linarith
    · -- a > b and ¬(a < b): so a > b, remaining is a - b ≥ 0
      linarith [h.1, h.2]
    · -- ¬(a > b) and a < b: so a < b, remaining is b - a ≥ 0  
      linarith [h.1, h.2]
    · -- ¬(a > b) and ¬(a < b): so a = b, remaining is b - b = 0
      linarith
  · norm_num
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int × Int :=
  (MaxDifferentDays a b, SameDays a b)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result: Int × Int) (h_precond : solve_precond a b) : Prop :=
  result.1 = MaxDifferentDays a b ∧
  result.2 = SameDays a b ∧
  result.1 ≥ 0 ∧
  result.2 ≥ 0 ∧
  result.1 ≤ a ∧ result.1 ≤ b

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact max_different_days_nonneg a b h_precond
  constructor
  · exact same_days_nonneg a b h_precond
  · exact max_different_days_le a b h_precond
-- </vc-theorems>

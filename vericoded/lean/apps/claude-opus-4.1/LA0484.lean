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
-- LLM HELPER
lemma correct_change_valid (n : Int) (h : ValidInput n) : ValidChange (CorrectChange n h) := by
  unfold CorrectChange ValidChange
  have h_mod_bounds : 0 ≤ n % 1000 ∧ n % 1000 < 1000 := by
    constructor
    · exact Int.emod_nonneg n (by norm_num : (1000 : Int) ≠ 0)
    · exact Int.emod_lt_of_pos n (by norm_num : 0 < (1000 : Int))
  constructor
  · -- 0 ≤ (1000 - n % 1000) % 1000
    apply Int.emod_nonneg
    norm_num
  · -- (1000 - n % 1000) % 1000 ≤ 999
    have h_lt : (1000 - n % 1000) % 1000 < 1000 := Int.emod_lt_of_pos _ (by norm_num : 0 < (1000 : Int))
    omega
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
  unfold solve_postcond solve
  exact ⟨correct_change_valid n h_precond, rfl⟩
-- </vc-theorems>

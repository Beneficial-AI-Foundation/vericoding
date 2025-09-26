import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 10 ∨ n ≤ -10

-- Helper functions for string manipulation (axiomatized for now)
noncomputable axiom IntToString : Int → String
noncomputable axiom StringToInt : String → Int

noncomputable def MaxBalanceAfterOperation (n : Int) : Int :=
  if n ≥ 0 then n
  else 
    let s := IntToString n
    let option1 := StringToInt (s.take (s.length - 1))
    let option2 := StringToInt (s.take (s.length - 2) ++ s.drop (s.length - 1))
    if option1 > option2 then option1 else option2

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem solve_precond_def (n : Int) : solve_precond n = ValidInput n := rfl
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (n : Int) (h_precond : solve_precond n) : Int :=
  MaxBalanceAfterOperation n
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  result = MaxBalanceAfterOperation n

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>

import Mathlib
-- <vc-preamble>
def ValidInput (t a b : Int) : Prop :=
  t > 0 ∧ a > 0 ∧ b > 0

def ValidOutput (res : String) : Prop :=
  res = "0" ∨ res = "1" ∨ res = "2" ∨ res = "inf"

def InfiniteCase (t a b : Int) : Prop :=
  a = t ∧ a = b ∧ a = 1

def TwoSolutionsCase (t a b : Int) : Prop :=
  a = t ∧ a = b ∧ a ≠ 1

def ZeroSolutionsCase (t a b : Int) : Prop :=
  (t = 2 ∧ a = 3 ∧ b > 10000) ∨
  (a = t ∧ a ≠ b) ∨
  (a ≠ t ∧ (a - b) % (t - a) = 0) ∨
  (a ≠ t ∧ (a - b) % (t - a) ≠ 0 ∧ t = b)

def OneSolutionCase (t a b : Int) : Prop :=
  a ≠ t ∧ (a - b) % (t - a) ≠ 0 ∧ t ≠ b

@[reducible, simp]
def solve_precond (t a b : Int) : Prop :=
  ValidInput t a b ∧ (t ≠ a ∨ a = t)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma not_special_case_from_mod (t a b : Int) : (a - b) % (t - a) ≠ 0 → ¬(t = 2 ∧ a = 3 ∧ b > 10000) := by
  rintro h_mod_ne_zero ⟨rfl, rfl, _⟩
  exact h_mod_ne_zero (by simp)
-- </vc-helpers>

-- <vc-definitions>
def solve (t a b : Int) (h_precond : solve_precond t a b) : String :=
  if a = t then
    if a = b then
      if a = 1 then
        "inf"
      else
        "2"
    else
      "0"
  else
    if (a - b) % (t - a) = 0 then
      "0"
    else
      if t = b then
        "0"
      else
        "1"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (t a b : Int) (result : String) (h_precond : solve_precond t a b) : Prop :=
  ValidOutput result ∧
  (InfiniteCase t a b → result = "inf") ∧
  (TwoSolutionsCase t a b → result = "2") ∧
  (ZeroSolutionsCase t a b → result = "0") ∧
  (OneSolutionCase t a b → result = "1")

theorem solve_spec_satisfied (t a b : Int) (h_precond : solve_precond t a b) :
    solve_postcond t a b (solve t a b h_precond) h_precond := by
  dsimp [solve, solve_postcond]
  split_ifs with h_at h_ab h_a1 h_mod h_tb

  -- Case 1: "inf" (a = t, a = b, a = 1)
  · simp_all [ValidOutput, InfiniteCase, TwoSolutionsCase, ZeroSolutionsCase, OneSolutionCase]

  -- Case 2: "2" (a = t, a = b, a ≠ 1)
  · simp_all [ValidOutput, InfiniteCase, TwoSolutionsCase, ZeroSolutionsCase, OneSolutionCase]

  -- Case 3: "0" (a = t, a ≠ b)
  · simp_all [ValidOutput, InfiniteCase, TwoSolutionsCase, ZeroSolutionsCase, OneSolutionCase]

  -- Case 4: "0" (a ≠ t, (a-b)%(t-a) = 0)
  · simp_all [ValidOutput, InfiniteCase, TwoSolutionsCase, ZeroSolutionsCase, OneSolutionCase]

  -- Case 5: "0" (a ≠ t, (a-b)%(t-a) ≠ 0, t = b)
  · simp_all [ValidOutput, InfiniteCase, TwoSolutionsCase, ZeroSolutionsCase, OneSolutionCase]

  -- Case 6: "1" (a ≠ t, (a-b)%(t-a) ≠ 0, t ≠ b)
  · simp_all [ValidOutput, InfiniteCase, TwoSolutionsCase, ZeroSolutionsCase, OneSolutionCase, not_special_case_from_mod]
-- </vc-theorems>

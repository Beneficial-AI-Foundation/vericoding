-- <vc-preamble>
def ValidInput (a b c : Int) : Prop :=
  1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 1 ≤ c ∧ c ≤ 100

def CountDistinctColors (a b c : Int) : Int :=
  if a = b ∧ b = c then 1
  else if a = b ∨ b = c ∨ a = c then 2
  else 3

def AllSame (a b c : Int) : Prop :=
  a = b ∧ b = c

def ExactlyTwoSame (a b c : Int) : Prop :=
  (a = b ∧ b ≠ c) ∨ (b = c ∧ a ≠ b) ∨ (a = c ∧ a ≠ b)

def AllDifferent (a b c : Int) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c

@[reducible, simp]
def solve_precond (a b c : Int) : Prop :=
  ValidInput a b c
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c : Int) (h_precond : solve_precond a b c) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c : Int) (result : Int) (h_precond : solve_precond a b c) : Prop :=
  1 ≤ result ∧ result ≤ 3 ∧
  result = CountDistinctColors a b c ∧
  (result = 1 ↔ AllSame a b c) ∧
  (result = 2 ↔ ExactlyTwoSame a b c) ∧
  (result = 3 ↔ AllDifferent a b c)

theorem solve_spec_satisfied (a b c : Int) (h_precond : solve_precond a b c) :
    solve_postcond a b c (solve a b c h_precond) h_precond := by
  sorry
-- </vc-theorems>
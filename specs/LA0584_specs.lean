-- <vc-preamble>
def ValidInput (A B C : Int) : Prop :=
  1 ≤ A ∧ A ≤ 100 ∧ 1 ≤ B ∧ B ≤ 100 ∧ 0 ≤ C ∧ C < B

def IsSolvable (A B C : Int) : Prop :=
  ∃ i, 1 ≤ i ∧ i < B ∧ (i * (A % B)) % B = C

@[reducible, simp]
def solve_precond (A B C : Int) : Prop :=
  ValidInput A B C
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (A B C : Int) (h_precond : solve_precond A B C) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B C : Int) (result: String) (h_precond : solve_precond A B C) : Prop :=
  (result = "YES" ↔ IsSolvable A B C) ∧ (result = "NO" ∨ result = "YES")

theorem solve_spec_satisfied (A B C : Int) (h_precond : solve_precond A B C) :
    solve_postcond A B C (solve A B C h_precond) h_precond := by
  sorry
-- </vc-theorems>
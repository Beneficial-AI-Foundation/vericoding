-- <vc-preamble>
noncomputable def CountNonZeroDigits : Int → Int := sorry
noncomputable def CountRange : Int → Int → Int → Int → Int := sorry

noncomputable def CountNumbersWithKNonZeroDigits (n k : Int) : Int :=
  CountRange n k 1 n

def ValidInput (n k : Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1 ∧ k ≤ 3

@[reducible, simp]
def solve_precond (N K : Int) : Prop :=
  ValidInput N K
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (N K : Int) (h_precond : solve_precond N K) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N K : Int) (count : Int) (h_precond : solve_precond N K) : Prop :=
  count = CountNumbersWithKNonZeroDigits N K ∧ count ≥ 0 ∧ count ≤ N

theorem solve_spec_satisfied (N K : Int) (h_precond : solve_precond N K) :
    solve_postcond N K (solve N K h_precond) h_precond := by
  sorry
-- </vc-theorems>

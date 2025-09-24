-- <vc-preamble>
def ValidInput (N : Int) (S : String) : Prop :=
  1 ≤ N ∧ N ≤ 100 ∧ S.length = N.natAbs ∧ ∀ i : Nat, i < S.length → 'a' ≤ S.data[i]! ∧ S.data[i]! ≤ 'z'

def IsConcatenationOfTwoCopies (S : String) : Prop :=
  S.length % 2 = 0 ∧ ∀ i : Nat, i < S.length / 2 → S.data[i]! = S.data[S.length / 2 + i]!

@[reducible, simp]
def solve_precond (N : Int) (S : String) : Prop :=
  ValidInput N S
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (S : String) (h_precond : solve_precond N S) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (S : String) (result : String) (h_precond : solve_precond N S) : Prop :=
  (result = "Yes" ∨ result = "No") ∧
  (N % 2 ≠ 0 → result = "No") ∧
  (N % 2 = 0 → (result = "Yes" ↔ IsConcatenationOfTwoCopies S))

theorem solve_spec_satisfied (N : Int) (S : String) (h_precond : solve_precond N S) :
    solve_postcond N S (solve N S h_precond) h_precond := by
  sorry
-- </vc-theorems>
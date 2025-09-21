-- <vc-preamble>
def ValidInput (n_A n_B k m : Int) (A B : List Int) : Prop :=
  n_A ≥ 1 ∧ n_B ≥ 1 ∧
  k ≥ 1 ∧ k ≤ n_A ∧
  m ≥ 1 ∧ m ≤ n_B ∧
  A.length = n_A ∧
  B.length = n_B

def IsSorted (s : List Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < s.length - 1 → s[i]! ≤ s[i + 1]!

def ValidSelection (A B : List Int) (k m : Int) : Prop :=
  k ≥ 1 ∧ k ≤ A.length ∧
  m ≥ 1 ∧ m ≤ B.length ∧
  A[(k - 1).natAbs]! < B[(B.length - m.natAbs)]!

@[reducible, simp]
def solve_precond (n_A n_B k m : Int) (A B : List Int) : Prop :=
  ValidInput n_A n_B k m A B ∧
  IsSorted A ∧
  IsSorted B
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n_A n_B k m : Int) (A B : List Int) (h_precond : solve_precond n_A n_B k m A B) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n_A n_B k m : Int) (A B : List Int) (result : String) (h_precond : solve_precond n_A n_B k m A B) : Prop :=
  (result = "YES" ∨ result = "NO") ∧
  (result = "YES" ↔ ValidSelection A B k m)

theorem solve_spec_satisfied (n_A n_B k m : Int) (A B : List Int) (h_precond : solve_precond n_A n_B k m A B) :
    solve_postcond n_A n_B k m A B (solve n_A n_B k m A B h_precond) h_precond := by
  sorry
-- </vc-theorems>
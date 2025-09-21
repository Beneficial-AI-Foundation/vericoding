-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 1

def ValidOutput (s : String) (n : Int) : Prop :=
  s.length = n.toNat ∧
  (∀ i : Nat, i < s.length → s.get ⟨i⟩ = 'a' ∨ s.get ⟨i⟩ = 'b' ∨ s.get ⟨i⟩ = 'c') ∧
  (∀ i : Nat, i + 2 < s.length → s.get ⟨i⟩ ≠ s.get ⟨i+2⟩)

def MinimalCUsage (s : String) : Prop :=
  ∀ i : Nat, i < s.length → s.get ⟨i⟩ = 'a' ∨ s.get ⟨i⟩ = 'b'

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : String) (h_precond : solve_precond n) : Prop :=
  ValidOutput result n ∧ MinimalCUsage result

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- <vc-preamble>
def StringToNat (s : String) : Nat :=
  s.toList.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def ValidInput (n : String) : Prop :=
  n.length > 0 ∧ 
  (∀ i, i < n.length → '0' ≤ n.data[i]! ∧ n.data[i]! ≤ '9') ∧
  (n.data[0]! ≠ '0' ∨ n.length = 1)

def ValidOutput (result : String) : Prop :=
  result = "4\n" ∨ result = "0\n"

@[reducible, simp]
def solve_precond (n : String) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : String) (h_precond : solve_precond n) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : String) (result : String) (h_precond : solve_precond n) : Prop :=
  ValidOutput result ∧
  ((StringToNat n % 4 = 0) ↔ (result = "4\n")) ∧
  ((StringToNat n % 4 ≠ 0) ↔ (result = "0\n"))

theorem solve_spec_satisfied (n : String) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>
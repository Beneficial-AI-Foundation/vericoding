-- <vc-preamble>
def ValidInput (n : Int) (a b : String) : Prop :=
  n > 0 ∧ a.length = 2 * n.natAbs ∧ b.length = 2 * n.natAbs ∧
  (∀ i : Nat, i < a.length → a.data[i]! = '0' ∨ a.data[i]! = '1') ∧
  (∀ i : Nat, i < b.length → b.data[i]! = '0' ∨ b.data[i]! = '1')

def CountPositions (a b : String) (ac bc : Char) (len : Int) : Int :=
  if len ≤ 0 then 0
  else (List.range len.natAbs).filter (fun i => 
    i < a.length ∧ i < b.length ∧ 
    a.data[i]! = ac ∧ b.data[i]! = bc
  ) |>.length

def ComputeGameOutcome (t00 t01 t10 t11 : Int) : Int :=
  t11 % 2 + (t10 - t01 + 1 - t11 % 2) / 2

def CorrectOutcome (result : String) (d : Int) : Prop :=
  (d > 0 → result = "First") ∧
  (d < 0 → result = "Second") ∧
  (d = 0 → result = "Draw")

@[reducible, simp]
def solve_precond (n : Int) (a b : String) : Prop :=
  ValidInput n a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a b : String) (h_precond : solve_precond n a b) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a b : String) (result : String) (h_precond : solve_precond n a b) : Prop :=
  (result = "First" ∨ result = "Second" ∨ result = "Draw") ∧
  (∃ t00 t01 t10 t11 : Int,
    t00 ≥ 0 ∧ t01 ≥ 0 ∧ t10 ≥ 0 ∧ t11 ≥ 0 ∧
    t00 + t01 + t10 + t11 = 2 * n ∧
    t00 = CountPositions a b '0' '0' (2 * n) ∧
    t01 = CountPositions a b '0' '1' (2 * n) ∧
    t10 = CountPositions a b '1' '0' (2 * n) ∧
    t11 = CountPositions a b '1' '1' (2 * n) ∧
    CorrectOutcome result (ComputeGameOutcome t00 t01 t10 t11))

theorem solve_spec_satisfied (n : Int) (a b : String) (h_precond : solve_precond n a b) :
    solve_postcond n a b (solve n a b h_precond) h_precond := by
  sorry
-- </vc-theorems>
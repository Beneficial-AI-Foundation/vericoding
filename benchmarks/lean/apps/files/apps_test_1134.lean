-- <vc-preamble>
def ValidInput (n : Nat) (m : List Int) : Prop :=
  n > 0 ∧ m.length = n ∧ 
  ∀ i, 0 ≤ i ∧ i < n → 0 ≤ m[i]! ∧ m[i]! < i + 1

def ValidSolution (n : Nat) (m : List Int) (dm : List Int) : Prop :=
  dm.length = n ∧ m.length = n ∧
  (∀ i, 0 ≤ i ∧ i < n → dm[i]! ≥ m[i]! + 1) ∧
  (∀ i, 0 ≤ i ∧ i < n - 1 → dm[i]! ≤ dm[i + 1]!)

def SumBelow (m : List Int) (dm : List Int) : Int :=
  match m with
  | [] => 0
  | head_m :: tail_m => 
    match dm with
    | [] => 0
    | head_dm :: tail_dm => (head_dm - 1 - head_m) + SumBelow tail_m tail_dm

@[reducible, simp]
def solve_precond (n : Nat) (m : List Int) : Prop :=
  ValidInput n m
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (m : List Int) (h_precond : solve_precond n m) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Nat) (m : List Int) (result : Int) (h_precond : solve_precond n m) : Prop :=
  result ≥ 0

theorem solve_spec_satisfied (n : Nat) (m : List Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  sorry
-- </vc-theorems>
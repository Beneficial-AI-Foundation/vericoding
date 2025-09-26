import Mathlib
-- <vc-preamble>
def countCellsHelper (n m i j : Nat) : Nat :=
  if i > n then 0
  else if j > n then countCellsHelper n m (i + 1) 1
  else 
    let count := if (i * i + j * j) % m = 0 then 1 else 0
    count + countCellsHelper n m i (j + 1)
termination_by (n + 1 - i, n + 1 - j)

def CountCellsDivisibleByM (n m : Int) : Int :=
  if n ≤ 0 ∨ m ≤ 0 then 0
  else Int.ofNat (countCellsHelper n.natAbs m.natAbs 1 1)

def ValidInput (n m : Int) : Prop :=
  1 ≤ n ∧ 1 ≤ m ∧ m ≤ 1000

@[reducible, simp]
def solve_precond (n m : Int) : Prop :=
  ValidInput n m
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (h_precond : solve_precond n m) : Int :=
  CountCellsDivisibleByM n m
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (result: Int) (h_precond : solve_precond n m) : Prop :=
  result ≥ 0 ∧ result = CountCellsDivisibleByM n m

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · -- prove result ≥ 0
    unfold CountCellsDivisibleByM
    split_ifs with h
    · simp
    · simp [Int.ofNat_nonneg]
  · -- prove result = CountCellsDivisibleByM n m
    rfl
-- </vc-theorems>

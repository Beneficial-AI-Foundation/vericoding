-- <vc-preamble>
def IsOdd (n : Int) : Bool :=
  n % 2 = 1

def CountDivisors (n : Nat) : Nat :=
  (List.range (n + 1)).filter (fun d => d ≥ 1 && d ≤ n && n % d = 0) |>.length

def HasEightDivisors (n : Nat) : Bool :=
  n > 0 && CountDivisors n = 8

def CountOddWithEightDivisors (N : Nat) : Nat :=
  (List.range (N + 1)).filter (fun i => i ≥ 1 && i ≤ N && IsOdd (Int.ofNat i) && i > 0 && HasEightDivisors i) |>.length

def ValidInput (N : Int) : Prop :=
  1 ≤ N ∧ N ≤ 200

@[reducible, simp]
def solve_precond (N : Int) : Prop :=
  ValidInput N
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (h_precond : solve_precond N) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (count : Int) (h_precond : solve_precond N) : Prop :=
  (N < 105 → count = 0) ∧
  (105 ≤ N ∧ N < 135 → count = 1) ∧
  (135 ≤ N ∧ N < 165 → count = 2) ∧
  (165 ≤ N ∧ N < 189 → count = 3) ∧
  (189 ≤ N ∧ N < 195 → count = 4) ∧
  (N ≥ 195 → count = 5) ∧
  (0 ≤ count ∧ count ≤ 5)

theorem solve_spec_satisfied (N : Int) (h_precond : solve_precond N) :
    solve_postcond N (solve N h_precond) h_precond := by
  sorry
-- </vc-theorems>
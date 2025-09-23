-- <vc-preamble>
def CommonDivisors (A B : Int) : List Int :=
  (List.range (A.natAbs + 1)).map (Int.ofNat) |>.filter (fun d => d > 0 ∧ d ≤ A ∧ A % d = 0 ∧ B % d = 0)

def ValidInput (A B K : Int) : Prop :=
  A > 0 ∧ B > 0 ∧ K ≥ 1 ∧ (CommonDivisors A B).length ≥ K

def IsKthLargestCommonDivisor (A B K result : Int) : Prop :=
  ValidInput A B K →
  result > 0 ∧
  A % result = 0 ∧ B % result = 0 ∧
  result ∈ CommonDivisors A B ∧
  ((CommonDivisors A B).filter (fun d => d > result)).length = K - 1

@[reducible, simp]
def solve_precond (A B K : Int) : Prop :=
  ValidInput A B K
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (A B K : Int) (h_precond : solve_precond A B K) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B K : Int) (result : Int) (h_precond : solve_precond A B K) : Prop :=
  IsKthLargestCommonDivisor A B K result

theorem solve_spec_satisfied (A B K : Int) (h_precond : solve_precond A B K) :
    solve_postcond A B K (solve A B K h_precond) h_precond := by
  sorry
-- </vc-theorems>
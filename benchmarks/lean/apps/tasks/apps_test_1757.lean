-- <vc-preamble>
partial def isFibHelper (num prev curr : Int) : Bool :=
  if curr = num then true
  else if curr > num then false
  else isFibHelper num curr (prev + curr)

def isFibonacci (num : Int) : Bool :=
  isFibHelper num 1 1

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  n ≥ 1 ∧ n ≤ 1000
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
  result.length = Int.natAbs n ∧
  (∀ i : Nat, i < result.length → result.toList.get? i = some 'O' ∨ result.toList.get? i = some 'o') ∧
  (∀ i : Int, 1 ≤ i ∧ i ≤ n → (isFibonacci i = true ↔ result.toList.get? (Int.natAbs (i-1)) = some 'O')) ∧
  (∀ i : Int, 1 ≤ i ∧ i ≤ n → (isFibonacci i = false ↔ result.toList.get? (Int.natAbs (i-1)) = some 'o'))

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>
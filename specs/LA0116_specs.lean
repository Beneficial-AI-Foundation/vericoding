-- <vc-preamble>
def DistinctNonZeroCount (arr : List Int) : Nat :=
  let nonZeros := arr.filter (· ≠ 0)
  let rec removeDuplicates : List Int → List Int
    | [] => []
    | x :: xs => 
      if xs.contains x then removeDuplicates xs
      else x :: removeDuplicates xs
  (removeDuplicates nonZeros).length

@[reducible, simp]
def solve_precond (arr : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (arr : List Int) (h_precond : solve_precond arr) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (arr : List Int) (result : Nat) (h_precond : solve_precond arr) : Prop :=
  result ≤ arr.length ∧ result = DistinctNonZeroCount arr

theorem solve_spec_satisfied (arr : List Int) (h_precond : solve_precond arr) :
    solve_postcond arr (solve arr h_precond) h_precond := by
  sorry
-- </vc-theorems>
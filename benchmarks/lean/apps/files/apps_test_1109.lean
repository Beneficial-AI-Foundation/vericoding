-- <vc-preamble>
def ValidInput (n k : Int) (A : List Int) : Prop :=
  1 ≤ k ∧ k ≤ n ∧ n ≤ 100 ∧
  n % k = 0 ∧
  A.length = n.natAbs ∧
  ∀ i, 0 ≤ i ∧ i < A.length → A[i]! = 1 ∨ A[i]! = 2

def CountOnesInColumn (A : List Int) (n k col : Int) : Int :=
  (List.range n.natAbs).filter (fun j => j % k.natAbs = col.natAbs ∧ j < A.length ∧ A[j]! = 1) |>.length

def CountTwosInColumn (A : List Int) (n k col : Int) : Int :=
  (List.range n.natAbs).filter (fun j => j % k.natAbs = col.natAbs ∧ j < A.length ∧ A[j]! = 2) |>.length

def MinChangesForColumn (A : List Int) (n k col : Int) : Int :=
  let count1 := CountOnesInColumn A n k col
  let count2 := CountTwosInColumn A n k col
  if count1 < count2 then count1 else count2

partial def SumMinChangesHelper (A : List Int) (n k col : Int) : Int :=
  if col = k then 0 
  else MinChangesForColumn A n k col + SumMinChangesHelper A n k (col + 1)

def SumMinChangesForAllColumns (A : List Int) (n k : Int) : Int :=
  SumMinChangesHelper A n k 0

@[reducible, simp]
def solve_precond (n k : Int) (A : List Int) : Prop :=
  ValidInput n k A
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (A : List Int) (h_precond : solve_precond n k A) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (A : List Int) (result : Int) (h_precond : solve_precond n k A) : Prop :=
  0 ≤ result ∧ result ≤ n ∧ result = SumMinChangesForAllColumns A n k

theorem solve_spec_satisfied (n k : Int) (A : List Int) (h_precond : solve_precond n k A) :
    solve_postcond n k A (solve n k A h_precond) h_precond := by
  sorry
-- </vc-theorems>
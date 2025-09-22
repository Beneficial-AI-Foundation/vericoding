-- <vc-preamble>
def isNonDecreasing (arr : List Int) (start : Int) (end_ : Int) : Prop :=
  0 ≤ start ∧ start ≤ end_ ∧ end_ < arr.length ∧
  ∀ i, start ≤ i ∧ i < end_ → arr[i.toNat]! ≤ arr[(i+1).toNat]!

def isNonIncreasing (arr : List Int) (start : Int) (end_ : Int) : Prop :=
  0 ≤ start ∧ start ≤ end_ ∧ end_ < arr.length ∧
  ∀ i, start ≤ i ∧ i < end_ → arr[i.toNat]! ≥ arr[(i+1).toNat]!

def isLadder (arr : List Int) (l : Int) (r : Int) : Prop :=
  0 ≤ l ∧ l ≤ r ∧ r < arr.length ∧
  (if l = r then True
   else ∃ k, l ≤ k ∧ k ≤ r ∧ isNonDecreasing arr l k ∧ isNonIncreasing arr k r)

@[reducible, simp]
def solve_precond (n m : Int) (arr : List Int) (queries : List (Int × Int)) : Prop :=
  n ≥ 1 ∧ m ≥ 1 ∧
  arr.length = n.toNat ∧
  queries.length = m.toNat ∧
  ∀ i, 0 ≤ i ∧ i < m → 1 ≤ queries[i.toNat]!.1 ∧ queries[i.toNat]!.1 ≤ queries[i.toNat]!.2 ∧ queries[i.toNat]!.2 ≤ n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (arr : List Int) (queries : List (Int × Int)) (h_precond : solve_precond n m arr queries) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (arr : List Int) (queries : List (Int × Int)) (results : List String) (h_precond : solve_precond n m arr queries) : Prop :=
  results.length = m.toNat ∧
  (∀ i, 0 ≤ i ∧ i < m → results[i.toNat]! = "Yes" ∨ results[i.toNat]! = "No") ∧
  (∀ i, 0 ≤ i ∧ i < m → (results[i.toNat]! = "Yes" ↔ isLadder arr (queries[i.toNat]!.1 - 1) (queries[i.toNat]!.2 - 1)))

theorem solve_spec_satisfied (n m : Int) (arr : List Int) (queries : List (Int × Int)) (h_precond : solve_precond n m arr queries) :
    solve_postcond n m arr queries (solve n m arr queries h_precond) h_precond := by
  sorry
-- </vc-theorems>
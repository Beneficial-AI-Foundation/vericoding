-- <vc-preamble>
def ValidInput (n : Int) (arr : List Int) : Prop :=
  n ≥ 1 ∧ arr.length = n.toNat ∧ ∀ i, 0 ≤ i ∧ i < arr.length → arr[i]! ≥ 1

def ValidOperations (operations : List (Int × Int)) (n : Int) : Prop :=
  ∀ op ∈ operations, 1 ≤ op.1 ∧ op.1 ≤ n ∧ 1 ≤ op.2 ∧ op.2 ≤ n ∧ op.2 = op.1 + 1

def isSorted (arr : List Int) : Bool :=
  if arr.length ≤ 1 then true
  else List.all (List.range (arr.length - 1)) (fun i => arr[i]! ≤ arr[i+1]!)

def swapAdjacent (arr : List Int) (i j : Nat) : List Int :=
  if i < arr.length ∧ j < arr.length ∧ j = i + 1 then
    arr.set i arr[j]!
  else arr

partial def applyOperations (arr : List Int) (operations : List (Int × Int)) : List Int :=
  match operations with
  | [] => arr
  | op :: rest => 
    if 1 ≤ op.1 ∧ op.1 ≤ arr.length ∧ 1 ≤ op.2 ∧ op.2 ≤ arr.length ∧ op.2 = op.1 + 1 then
      let newArr := swapAdjacent arr (op.1.toNat - 1) (op.2.toNat - 1)
      applyOperations newArr rest
    else
      applyOperations arr rest

def countInversions (arr : List Int) : Nat :=
  (List.range arr.length).foldl (fun acc i =>
    acc + (List.range arr.length).foldl (fun acc2 j =>
      if i < j ∧ arr[i]! > arr[j]! then acc2 + 1 else acc2) 0) 0

@[reducible, simp]
def solve_precond (n : Int) (arr : List Int) : Prop :=
  ValidInput n arr
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (arr : List Int) (h_precond : solve_precond n arr) : List (Int × Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (arr : List Int) (operations : List (Int × Int)) (h_precond : solve_precond n arr) : Prop :=
  ValidOperations operations n ∧
  (let finalArr := applyOperations arr operations; isSorted finalArr = true ∨ operations.length = 20000) ∧
  (∀ x, x ∈ arr ↔ x ∈ applyOperations arr operations) ∧
  operations.length ≤ 20000 ∧
  (isSorted arr = true → operations.length = 0)

theorem solve_spec_satisfied (n : Int) (arr : List Int) (h_precond : solve_precond n arr) :
    solve_postcond n arr (solve n arr h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- <vc-preamble>
def ValidInput (A : Array Int) : Prop :=
  A.size ≥ 2 ∧ ∀ i, i < A.size → A[i]! ≥ 1

def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

def ValidPair (A : Array Int) (i j : Nat) : Prop :=
  i < A.size ∧ j < A.size ∧ 
  i ≠ j ∧ abs ((i + 1 : Int) - (j + 1 : Int)) = A[i]! + A[j]!

instance (A : Array Int) (i j : Nat) : Decidable (ValidPair A i j) := by
  unfold ValidPair
  infer_instance

def CountValidPairs (A : Array Int) : Int :=
  (List.range A.size).foldl (fun acc i =>
    acc + (List.range A.size).foldl (fun acc2 j =>
      if ValidPair A i j then acc2 + 1 else acc2) 0) 0

@[reducible, simp]
def solve_precond (A : Array Int) : Prop :=
  ValidInput A
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (A : Array Int) (h_precond : solve_precond A) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A : Array Int) (result : Int) (h_precond : solve_precond A) : Prop :=
  result ≥ 0 ∧ result = CountValidPairs A

theorem solve_spec_satisfied (A : Array Int) (h_precond : solve_precond A) :
    solve_postcond A (solve A h_precond) h_precond := by
  sorry
-- </vc-theorems>
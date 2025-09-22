-- <vc-preamble>
def ValidInput (n k : Int) (A : List Int) : Prop :=
  k > 0 ∧ A.length = k ∧ (∀ i, 0 ≤ i ∧ i < k → A[Int.natAbs i]! > 0) ∧ n ≥ 0

def HamstersTransported (n capacity : Int) : Int :=
  capacity * (n / capacity)

def OptimalSolution (n : Int) (A : List Int) (box_type num_boxes : Int) : Prop :=
  ValidInput n A.length A ∧ 
  1 ≤ box_type ∧ box_type ≤ A.length ∧
  num_boxes = n / A[Int.natAbs (box_type - 1)]! ∧
  ∀ i, 0 ≤ i ∧ i < A.length → 
    HamstersTransported n A[Int.natAbs (box_type - 1)]! ≥ HamstersTransported n A[Int.natAbs i]!

@[reducible, simp]
def solve_precond (n k : Int) (A : List Int) : Prop :=
  ValidInput n k A
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (A : List Int) (h_precond : solve_precond n k A) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (A : List Int) (result : Int × Int) (h_precond : solve_precond n k A) : Prop :=
  1 ≤ result.1 ∧ result.1 ≤ k ∧
  result.2 ≥ 0 ∧
  OptimalSolution n A result.1 result.2

theorem solve_spec_satisfied (n k : Int) (A : List Int) (h_precond : solve_precond n k A) :
    solve_postcond n k A (solve n k A h_precond) h_precond := by
  sorry
-- </vc-theorems>
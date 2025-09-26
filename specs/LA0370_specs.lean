-- <vc-preamble>
@[reducible, simp]
def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 2 ∧ a.length = Int.natAbs n

def CountViolationsForK (a : List Int) (n : Int) (k : Int) : Int :=
  if n ≥ 2 ∧ a.length = Int.natAbs n ∧ 1 ≤ k ∧ k ≤ n - 1 then
    (List.range (Int.natAbs n + 1)).filter (fun i => 
      i ≥ 2 ∧ i ≤ Int.natAbs n ∧
      let parent_idx := (i + Int.natAbs k - 2) / Int.natAbs k
      parent_idx ≥ 1 ∧ i - 1 < a.length ∧ parent_idx - 1 < a.length ∧ 
      a.get! (i - 1) < a.get! (parent_idx - 1)) |>.length
  else 0

@[reducible, simp]
def ValidOutput (result : List Int) (n : Int) (a : List Int) : Prop :=
  n ≥ 2 ∧ a.length = Int.natAbs n →
  result.length = Int.natAbs n - 1 ∧
  (∀ k, 1 ≤ k ∧ k ≤ n - 1 → k - 1 < result.length ∧ result.get! (Int.natAbs k - 1) ≥ 0) ∧
  (∀ k, 1 ≤ k ∧ k ≤ n - 1 → k - 1 < result.length ∧ result.get! (Int.natAbs k - 1) = CountViolationsForK a n k)

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : List Int) (h_precond : solve_precond n a) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (result : List Int) (h_precond : solve_precond n a) : Prop :=
  ValidOutput result n a

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>
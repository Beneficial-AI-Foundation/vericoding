-- <vc-preamble>
def maxHeightUpTo (heights : List Int) (up_to_index : Nat) : Int :=
  if up_to_index = 0 then heights[0]!
  else if heights[up_to_index]! ≥ maxHeightUpTo heights (up_to_index - 1) then heights[up_to_index]!
  else maxHeightUpTo heights (up_to_index - 1)
termination_by up_to_index

def hasOceanVisibility (heights : List Int) (mountain_index : Nat) : Bool :=
  mountain_index = 0 || heights[mountain_index]! ≥ maxHeightUpTo heights (mountain_index - 1)

@[reducible, simp]
def solve_precond (N : Int) (heights : List Int) : Prop :=
  N > 0 ∧ heights.length = N.toNat ∧ N ≤ 20 ∧ ∀ i, 0 ≤ i ∧ i < N → 1 ≤ heights[i.toNat]! ∧ heights[i.toNat]! ≤ 100
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (heights : List Int) (h_precond : solve_precond N heights) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (heights : List Int) (result : Int) (h_precond : solve_precond N heights) : Prop :=
  1 ≤ result ∧ result ≤ N ∧ result = ((List.range N.toNat).filter (fun i => hasOceanVisibility heights i)).length

theorem solve_spec_satisfied (N : Int) (heights : List Int) (h_precond : solve_precond N heights) :
    solve_postcond N heights (solve N heights h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- <vc-preamble>
@[reducible]
def semiOrderedPermutation_precond (nums : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def semiOrderedPermutation (nums : List Int) (h_precond : semiOrderedPermutation_precond (nums)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def semiOrderedPermutation_postcond (nums : List Int) (result: Int) (h_precond : semiOrderedPermutation_precond (nums)) : Prop :=
  let n := nums.length
  let pos1 := nums.idxOf 1
  let posn := nums.idxOf (Int.ofNat n)
  if pos1 > posn then
    pos1 + n = result + 2 + posn
  else
    pos1 + n = result + 1 + posn

theorem semiOrderedPermutation_spec_satisfied (nums: List Int) (h_precond : semiOrderedPermutation_precond (nums)) :
    semiOrderedPermutation_postcond (nums) (semiOrderedPermutation (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>
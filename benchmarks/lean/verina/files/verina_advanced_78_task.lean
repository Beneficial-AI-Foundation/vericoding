-- <vc-preamble>
@[reducible]
def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  let pairwiseSum := List.range nums.length |>.flatMap (fun i =>
    nums.drop (i + 1) |>.map (fun y => nums[i]! + y))
  nums.length > 1 ∧ pairwiseSum.count target = 1
-- </vc-preamble>

-- <vc-helpers>
def findComplement (nums : List Int) (target : Int) (i : Nat) (x : Int) : Option Nat :=
  let rec aux (nums : List Int) (j : Nat) : Option Nat :=
    match nums with
    | []      => none
    | y :: ys => if x + y = target then some (i + j + 1) else aux ys (j + 1)
  aux nums 0

def twoSumAux (nums : List Int) (target : Int) (i : Nat) : Prod Nat Nat :=
  match nums with
  | []      => panic! "No solution exists"
  | x :: xs =>
    match findComplement xs target i x with
    | some j => (i, j)
    | none   => twoSumAux xs target (i + 1)
-- </vc-helpers>

-- <vc-definitions>
def twoSum (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Prod Nat Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def twoSum_postcond (nums : List Int) (target : Int) (result: Prod Nat Nat) (h_precond : twoSum_precond (nums) (target)) : Prop :=
  let i := result.fst;
  let j := result.snd;
  (i < j) ∧
  (i < nums.length) ∧ (j < nums.length) ∧
  (nums[i]!) + (nums[j]!) = target

theorem twoSum_spec_satisfied (nums: List Int) (target: Int) (h_precond : twoSum_precond (nums) (target)) :
    twoSum_postcond (nums) (target) (twoSum (nums) (target) h_precond) h_precond := by
  sorry
-- </vc-theorems>
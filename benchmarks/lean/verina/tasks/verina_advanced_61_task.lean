-- <vc-preamble>
@[reducible]
def productExceptSelf_precond (nums : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- Helper: Compute prefix products.
-- prefix[i] is the product of all elements in nums before index i.
def computepref (nums : List Int) : List Int :=
  nums.foldl (fun acc x => acc ++ [acc.getLast! * x]) [1]

-- Helper: Compute suffix products.
-- suffix[i] is the product of all elements in nums from index i (inclusive) to the end.
-- We reverse the list and fold, then reverse back.
def computeSuffix (nums : List Int) : List Int :=
  let revSuffix := nums.reverse.foldl (fun acc x => acc ++ [acc.getLast! * x]) [1]
  revSuffix.reverse
-- </vc-helpers>

-- <vc-definitions>
def productExceptSelf (nums : List Int) (h_precond : productExceptSelf_precond (nums)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
-- Specification Helper: Product of a list of Ints
-- Defined locally if not available/imported
def List.myprod : List Int → Int
  | [] => 1
  | x :: xs => x * xs.myprod
@[reducible]
def productExceptSelf_postcond (nums : List Int) (result: List Int) (h_precond : productExceptSelf_precond (nums)) : Prop :=
  nums.length = result.length ∧
  (List.range nums.length |>.all (fun i =>
    result[i]! = some (((List.take i nums).myprod) * ((List.drop (i+1) nums).myprod))))

theorem productExceptSelf_spec_satisfied (nums: List Int) (h_precond : productExceptSelf_precond (nums)) :
    productExceptSelf_postcond (nums) (productExceptSelf (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>
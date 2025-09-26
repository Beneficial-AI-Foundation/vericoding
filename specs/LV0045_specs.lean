-- <vc-preamble>
@[reducible, simp]
def maxSubarraySum_precond (numbers : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxSubarraySum (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def maxSubarraySum_postcond (numbers : List Int) (result: Int) (h_precond : maxSubarraySum_precond (numbers)) : Prop :=
  let subArraySums :=
    List.range (numbers.length + 1) |>.flatMap (fun start =>
      List.range (numbers.length - start + 1) |>.map (fun len =>
        numbers.drop start |>.take len |>.sum))
  subArraySums.contains result ∧ subArraySums.all (· ≤ result)

theorem maxSubarraySum_spec_satisfied (numbers: List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    maxSubarraySum_postcond (numbers) (maxSubarraySum (numbers) h_precond) h_precond := by
  sorry
-- </vc-theorems>
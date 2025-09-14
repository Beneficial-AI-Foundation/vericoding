// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method solution(nums: array<int>) returns (result: int)
    requires
        1 <= nums.Length <= 100
    requires
        forall i :: 0 <= i < nums.Length ==> nums[i] >= 1 && nums[i] <= 100
    ensures
        result >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added loop invariant to ensure minimum remains >=1 for postcondition */
  var current := nums[0];
  for i := 1 to nums.Length
    invariant current >= 1
  {
    current := min(current, nums[i]);
  }
  result := current;
}
// </vc-code>

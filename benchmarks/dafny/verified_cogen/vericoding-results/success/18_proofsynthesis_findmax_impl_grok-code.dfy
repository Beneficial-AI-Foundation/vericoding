// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindMax(nums: array<int>) returns (ret: int)
    requires nums.Length > 0
    ensures forall i :: 0 <= i < nums.Length ==> nums[i] <= ret
    ensures exists i :: 0 <= i < nums.Length && nums[i] == ret
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 2): Removed the explicit decreases clause from the for loop to fix compilation error, as it is only allowed with 'to *' syntax. */
var maxSoFar := nums[0];
for i := 1 to nums.Length
  invariant forall k :: 0 <= k < i ==> nums[k] <= maxSoFar
  invariant exists k :: 0 <= k < i && nums[k] == maxSoFar
{
  if nums[i] > maxSoFar {
    maxSoFar := nums[i];
  }
}
ret := maxSoFar;
}
// </vc-code>

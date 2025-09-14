// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): renamed min to Minimum to resolve shadowing and compilation error */
function Minimum(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method SmallestNum(nums: array<int>) returns (min: int)
    requires nums.Length > 0
    ensures forall i :: 0 <= i < nums.Length ==> min <= nums[i]
    ensures exists i :: 0 <= i < nums.Length && min == nums[i]
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): updated min function calls to Minimum to fix compilation error and ensure verification */
  min := nums[0];
  var i := 1;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall j :: 0 <= j < i ==> min <= nums[j]
    invariant exists j :: 0 <= j < i && min == nums[j]
  {
    min := Minimum(min, nums[i]);
    i := i + 1;
  }
}
// </vc-code>

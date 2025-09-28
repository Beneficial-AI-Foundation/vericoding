// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Squared(x: int): int { x * x }
predicate BoundsCheck(x: int) { 0 <= x * x < 2147483647 }
// </vc-helpers>

// <vc-spec>
method SquareNums(nums: array<int>) returns (squared: array<int>)
    requires
        forall k :: 0 <= k < nums.Length ==> (0 <= nums[k] * nums[k] < 2147483647)
    ensures
        nums.Length == squared.Length
    ensures
        forall k :: 0 <= k < nums.Length ==> (squared[k] == nums[k] * nums[k])
// </vc-spec>
// <vc-code>
{
  squared := new int[nums.Length];
  var i: int := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall k :: 0 <= k < i ==> squared[k] == nums[k] * nums[k]
  {
    squared[i] := nums[i] * nums[i];
    i := i + 1;
  }
}
// </vc-code>

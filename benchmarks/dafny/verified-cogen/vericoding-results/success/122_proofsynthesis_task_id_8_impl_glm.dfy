// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsInRange(num: int): bool { 0 <= num * num < 2147483647 }
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
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant forall j :: 0 <= j < i ==> squared[j] == nums[j] * nums[j]
    {
        if IsInRange(nums[i]) {
            squared[i] := nums[i] * nums[i];
        } else {
            squared[i] := 0;
        }
        i := i + 1;
    }
}
// </vc-code>

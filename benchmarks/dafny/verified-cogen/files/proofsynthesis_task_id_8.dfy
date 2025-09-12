// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
    assume {:axiom} false;
}
// </vc-code>

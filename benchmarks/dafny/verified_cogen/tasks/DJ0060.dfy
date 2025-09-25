// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SmallestNum(nums: array<int>) returns (min: int)
    requires nums.Length > 0
    ensures forall i :: 0 <= i < nums.Length ==> min <= nums[i]
    ensures exists i :: 0 <= i < nums.Length && min == nums[i]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>

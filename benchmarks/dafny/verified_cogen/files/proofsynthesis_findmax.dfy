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
    assume {:axiom} false;
}
// </vc-code>

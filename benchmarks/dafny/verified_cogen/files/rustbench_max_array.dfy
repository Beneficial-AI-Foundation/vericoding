// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MaxArray(nums: array<int>) returns (idx: int)
    requires
        nums.Length >= 1
    ensures
        0 <= idx && idx < nums.Length &&
        forall i :: 0 <= i && i < nums.Length ==> nums[i] <= nums[idx]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>

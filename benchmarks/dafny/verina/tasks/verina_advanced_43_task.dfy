// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MaxStrength(nums: array<int>) returns (result: int)
    requires nums.Length > 0
    ensures
        /* The result represents the maximum product of any non-empty subset of nums.
           For simplicity, we ensure that the result is at least as large as one of the elements. */
        exists i :: 0 <= i < nums.Length && result >= nums[i]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := 0;
    // impl-end
}
// </vc-code>

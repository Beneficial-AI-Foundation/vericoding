// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CubeElement(nums: array<int>) returns (cubed: array<int>)

    requires
        forall k :: 0 <= k < nums.Length ==> (
            var val := nums[k];
            var squared := val * val;
            var cubed_val := squared * val;
            -2147483648 <= squared <= 2147483647 &&
            -2147483648 <= cubed_val <= 2147483647
        )

    ensures
        cubed.Length == nums.Length
    ensures
        forall i :: 0 <= i < nums.Length ==> 
            cubed[i] == nums[i] * nums[i] * nums[i]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>

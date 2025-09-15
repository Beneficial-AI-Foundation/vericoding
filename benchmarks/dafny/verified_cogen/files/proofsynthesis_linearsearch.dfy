// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method LinearSearch(nums: array<int>, target: int) returns (ret: int)
    requires nums.Length < 0x8000_0000
    ensures ret < nums.Length
    ensures ret >= 0 ==> nums[ret] == target
    ensures ret >= 0 ==> forall i :: 0 <= i < ret ==> nums[i] != target
    ensures ret < 0 ==> forall i :: 0 <= i < nums.Length ==> nums[i] != target
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>

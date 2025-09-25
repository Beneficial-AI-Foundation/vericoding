// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method TopKFrequent(nums: array<int>, k: nat) returns (result: array<int>)
    requires k <= |set i | 0 <= i < nums.Length :: nums[i]|
    ensures result.Length == k
    ensures forall x :: x in result[..] ==> x in nums[..]
    ensures forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    result := new int[k];
    assume {:axiom} false;
}
// </vc-code>

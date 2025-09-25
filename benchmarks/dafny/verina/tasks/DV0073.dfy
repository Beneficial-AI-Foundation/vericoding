// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solution(nums: array<int>) returns (result: int)
    requires
        1 <= nums.Length <= 100
    requires
        forall i :: 0 <= i < nums.Length ==> nums[i] >= 1 && nums[i] <= 100
    ensures
        result >= 0
// </vc-spec>
// <vc-code>
{
    // TODO: implement
    result := 0;
}
// </vc-code>

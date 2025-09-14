// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added ensures clause to guarantee non-negative result */
function LISHelper(nums: array<int>, i: int, last: int): int
    requires 0 <= i <= nums.Length
    reads nums
    decreases nums.Length - i
    ensures LISHelper(nums, i, last) >= 0
{
    if i == nums.Length then 0
    else
        var skip := LISHelper(nums, i + 1, last);
        if nums[i] > last then
            var take := 1 + LISHelper(nums, i + 1, nums[i]);
            if take > skip then take else skip
        else
            skip
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(nums: array<int>) returns (result: int)
    ensures result >= 0
    ensures nums.Length == 0 ==> result == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): no changes needed as helper now guarantees non-negative result */
    if nums.Length == 0 {
        result := 0;
    } else {
        result := LISHelper(nums, 0, -2147483648);
    }
}
// </vc-code>

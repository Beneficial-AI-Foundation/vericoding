// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove unused helper */
function Nothing(x: int): int { x }
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
/* code modified by LLM (iteration 5): No changes needed, previous implementation was correct */
{
    var i: int := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant forall k :: 0 <= k < i ==> nums[k] != target
    {
        if nums[i] == target {
            return i;
        }
        i := i + 1;
    }
    return -1;
}
// </vc-code>

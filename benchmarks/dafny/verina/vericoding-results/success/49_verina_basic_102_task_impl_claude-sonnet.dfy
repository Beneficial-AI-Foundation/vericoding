// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed non-compilable function with unbounded quantifier */
predicate ValidPair(nums: array<int>, target: int, i: int, j: int)
    reads nums
{
    0 <= i < j < nums.Length && nums[i] + nums[j] == target
}
// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (result: (int, int))
    requires 
        nums.Length > 1 &&
        (exists i: int, j: int :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target)
    ensures
        0 <= result.0 < result.1 < nums.Length &&
        nums[result.0] + nums[result.1] == target &&
        (forall i: int, j: int :: 0 <= i < j < nums.Length && i < result.0 ==> nums[i] + nums[j] != target)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Keeping working nested loop implementation */
    var i := 0;
    while i < nums.Length - 1
        invariant 0 <= i <= nums.Length - 1
        invariant forall x: int, y: int :: 0 <= x < y < nums.Length && x < i ==> nums[x] + nums[y] != target
    {
        var j := i + 1;
        while j < nums.Length
            invariant i + 1 <= j <= nums.Length
            invariant forall y: int :: i + 1 <= y < j ==> nums[i] + nums[y] != target
        {
            if nums[i] + nums[j] == target {
                result := (i, j);
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    result := (0, 1);
}
// </vc-code>

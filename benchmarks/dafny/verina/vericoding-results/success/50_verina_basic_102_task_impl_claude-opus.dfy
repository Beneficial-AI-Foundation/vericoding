// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
    var i := 0;
    while i < nums.Length - 1
        invariant 0 <= i < nums.Length
        invariant forall k: int, j: int :: 0 <= k < i && k < j < nums.Length ==> nums[k] + nums[j] != target
        decreases nums.Length - i
    {
        var j := i + 1;
        while j < nums.Length
            invariant i + 1 <= j <= nums.Length
            invariant forall k: int :: i + 1 <= k < j ==> nums[i] + nums[k] != target
            decreases nums.Length - j
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

// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
method ensureLengthOne(nums: array<int>) returns (r: int)
    requires nums.Length == 1
    ensures r == 0
{
    r := 0;
}

method minimumDifferenceHelper(nums: array<int>, i: int, j: int) returns (minDiff: int)
    requires 0 <= i < nums.Length
    requires 0 <= j < nums.Length
    requires i != j
    ensures minDiff >= 0
{
    minDiff := if nums[i] > nums[j] then nums[i] - nums[j] else nums[j] - nums[i];
}
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
    if nums.Length == 1 {
        result := ensureLengthOne(nums);
        return;
    }
    
    result := 100; // max possible diff is 99
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant result >= 0
    {
        var j := i + 1;
        while j < nums.Length
            invariant i + 1 <= j <= nums.Length
            invariant result >= 0
        {
            var diff := minimumDifferenceHelper(nums, i, j);
            if diff < result {
                result := diff;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

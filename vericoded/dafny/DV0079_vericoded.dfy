// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (result: array<int>)
    requires 
        nums.Length >= 2 &&
        (exists i: int, j: int :: 0 <= j < i < nums.Length && nums[i] + nums[j] == target) &&
        (forall i1: int, j1: int, i2: int, j2: int :: 
            (0 <= j1 < i1 < nums.Length && nums[i1] + nums[j1] == target &&
             0 <= j2 < i2 < nums.Length && nums[i2] + nums[j2] == target) ==> 
            (i1 == i2 && j1 == j2))
    ensures
        result.Length == 2 &&
        0 <= result[0] < nums.Length &&
        0 <= result[1] < nums.Length &&
        result[0] < result[1] &&
        nums[result[0]] + nums[result[1]] == target
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed index ordering to ensure result[0] < result[1] */
    result := new int[2];
    var i := 0;
    var found := false;
    
    while i < nums.Length && !found
        invariant 0 <= i <= nums.Length
        invariant !found ==> forall i': int, j': int :: 0 <= j' < i' < i ==> nums[i'] + nums[j'] != target
        invariant found ==> result.Length == 2 && 0 <= result[0] < result[1] < nums.Length && nums[result[0]] + nums[result[1]] == target
    {
        var j := 0;
        while j < i && !found
            invariant 0 <= j <= i < nums.Length
            invariant !found ==> forall j': int :: 0 <= j' < j ==> nums[i] + nums[j'] != target
            invariant found ==> result.Length == 2 && 0 <= result[0] < result[1] < nums.Length && nums[result[0]] + nums[result[1]] == target
        {
            if nums[i] + nums[j] == target {
                result[0] := j;
                result[1] := i;
                found := true;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

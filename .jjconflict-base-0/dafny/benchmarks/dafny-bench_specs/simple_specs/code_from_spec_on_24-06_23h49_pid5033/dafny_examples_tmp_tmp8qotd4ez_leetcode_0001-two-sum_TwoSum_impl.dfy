//IMPL TwoSum
method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
 ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
            nums[r.0] + nums[r.1] == target &&
            forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
 ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        /* code modified by LLM (iteration 2): Fixed outer loop invariant to properly capture all checked pairs */
        invariant forall x, y :: 0 <= x < y < nums.Length && x < i ==> nums[x] + nums[y] != target
    {
        var j := i + 1;
        while j < nums.Length
            invariant i + 1 <= j <= nums.Length
            /* code modified by LLM (iteration 2): Maintained outer invariant in inner loop */
            invariant forall x, y :: 0 <= x < y < nums.Length && x < i ==> nums[x] + nums[y] != target
            invariant forall y :: i + 1 <= y < j ==> nums[i] + nums[y] != target
        {
            if nums[i] + nums[j] == target {
                /* code modified by LLM (iteration 2): Simplified proof with correct invariant assumptions */
                assert 0 <= i < j < nums.Length;
                assert nums[i] + nums[j] == target;
                
                /* code modified by LLM (iteration 2): Prove the forall condition holds for all pairs before j */
                forall x, y | 0 <= x < y < j ensures nums[x] + nums[y] != target {
                    if x < i {
                        // From outer loop invariant
                    } else {
                        // x == i, and from inner loop invariant
                        assert x == i && i + 1 <= y < j;
                    }
                }
                
                return (i, j);
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 2): When loop exits, all pairs have been checked */
    return (-1, -1);
}
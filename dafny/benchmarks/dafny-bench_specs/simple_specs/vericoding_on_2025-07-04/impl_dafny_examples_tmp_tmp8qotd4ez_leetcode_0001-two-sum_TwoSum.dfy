//IMPL 
method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
 ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
            nums[r.0] + nums[r.1] == target &&
            forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
 ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{
    var i := 0;
    while i < nums.Length
        /* code modified by LLM (iteration 4): Fixed invariant to properly track all checked pairs */
        invariant 0 <= i <= nums.Length
        invariant forall x, y :: 0 <= x < y < nums.Length && x < i ==> nums[x] + nums[y] != target
    {
        var j := i + 1;
        while j < nums.Length
            invariant i + 1 <= j <= nums.Length
            invariant forall y :: i < y < j ==> nums[i] + nums[y] != target
        {
            if nums[i] + nums[j] == target {
                /* code modified by LLM (iteration 4): Added assertions to help prove the ensures clauses */
                assert 0 <= i < j < nums.Length;
                assert nums[i] + nums[j] == target;
                assert forall x, y :: 0 <= x < y < j && x < i ==> nums[x] + nums[y] != target;
                assert forall y :: i < y < j ==> nums[i] + nums[y] != target;
                assert forall x, y :: 0 <= x < y < j ==> nums[x] + nums[y] != target;
                return (i, j);
            }
            j := j + 1;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 4): Simplified final assertion */
    assert forall x, y :: 0 <= x < y < nums.Length ==> nums[x] + nums[y] != target;
    return (-1, -1);
}
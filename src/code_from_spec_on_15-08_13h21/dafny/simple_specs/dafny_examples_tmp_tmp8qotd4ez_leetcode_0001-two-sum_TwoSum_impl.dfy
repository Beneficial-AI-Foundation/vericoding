method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
ensures 0 <= r.0 ==> (0 <= r.0 < r.1 < nums.Length && 
           nums[r.0] + nums[r.1] == target &&
           forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target)
ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        /* code modified by LLM (iteration 1): strengthened invariant to track all pairs with both indices less than i */
        invariant forall x, y :: 0 <= x < y < nums.Length && y < i ==> nums[x] + nums[y] != target
    {
        var j := i + 1;
        while j < nums.Length
            invariant i + 1 <= j <= nums.Length
            invariant forall y :: i < y < j ==> nums[i] + nums[y] != target
            /* code modified by LLM (iteration 1): strengthened invariant to include all pairs before current position */
            invariant forall x, y :: 0 <= x < y < nums.Length && (y < i || (x == i && y < j)) ==> nums[x] + nums[y] != target
        {
            if nums[i] + nums[j] == target {
                /* code modified by LLM (iteration 1): simplified assertion using the strengthened invariant */
                assert forall x, y :: 0 <= x < y < j ==> nums[x] + nums[y] != target;
                r := (i, j);
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    r := (-1, -1);
}
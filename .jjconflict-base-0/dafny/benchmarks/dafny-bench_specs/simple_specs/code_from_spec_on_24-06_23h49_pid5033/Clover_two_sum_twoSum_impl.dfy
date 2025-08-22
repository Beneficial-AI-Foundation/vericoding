//IMPL twoSum
method twoSum(nums: array<int>, target: int) returns (i: int, j: int)
 requires nums.Length > 1
 requires exists i,j::0 <= i < j < nums.Length && nums[i] + nums[j] == target
 ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
 ensures forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length) ==> nums[ii] + nums[jj] != target
 ensures forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
{
    i := 0;
    while i < nums.Length - 1
        invariant 0 <= i < nums.Length
        invariant forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length) ==> nums[ii] + nums[jj] != target
    {
        j := i + 1;
        while j < nums.Length
            invariant i < j <= nums.Length
            invariant forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
        {
            if nums[i] + nums[j] == target {
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}


// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method twoSum(nums: array<int>, target: int) returns (i: int, j: int)
  requires nums.Length > 1
  requires exists i,j::0 <= i < j < nums.Length &&  nums[i] + nums[j] == target
  ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  ensures forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length)  ==> nums[ii] + nums[jj] != target
  ensures forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
// </vc-spec>
// <vc-code>
{
    i := 0;
    j := 1;
    
    while i < nums.Length - 1
        invariant 0 <= i < nums.Length
        invariant forall ii, jj :: 0 <= ii < i && ii < jj < nums.Length ==> nums[ii] + nums[jj] != target
        decreases nums.Length - i
    {
        j := i + 1;
        
        while j < nums.Length
            invariant i + 1 <= j <= nums.Length
            invariant forall jj :: i < jj < j ==> nums[i] + nums[jj] != target
            decreases nums.Length - j
        {
            if nums[i] + nums[j] == target {
                return;
            }
            j := j + 1;
        }
        
        i := i + 1;
    }
    
    // This point should be unreachable due to the precondition
    assert false;
}
// </vc-code>


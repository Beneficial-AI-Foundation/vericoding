method RemoveDuplicates(nums: array<int>) returns (num_length: int)
 modifies nums
 requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
 ensures nums.Length == nums.Length
 ensures 0 <= num_length <= nums.Length
 ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
 ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
 ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
{
    if nums.Length == 0 {
        num_length := 0;
        return;
    }
    
    /* code modified by LLM (iteration 4): store original array content to satisfy postconditions */
    ghost var original := nums[..];
    
    num_length := 1;
    var i := 1;
    
    while i < nums.Length
        invariant 1 <= num_length <= i <= nums.Length
        /* code modified by LLM (iteration 4): elements in result portion are distinct */
        invariant forall k, l | 0 <= k < l < num_length :: nums[k] != nums[l]
        /* code modified by LLM (iteration 4): elements in result come from original */
        invariant forall k | 0 <= k < num_length :: nums[k] in original
        /* code modified by LLM (iteration 4): every unique value from processed portion appears in result */
        invariant forall val | val in original[..i] :: exists k | 0 <= k < num_length :: nums[k] == val
        /* code modified by LLM (iteration 4): result portion remains sorted */
        invariant forall k, l | 0 <= k < l < num_length :: nums[k] < nums[l]
        /* code modified by LLM (iteration 4): result preserves sorted order from original */
        invariant forall k | 0 <= k < num_length :: exists j | 0 <= j < i :: nums[k] == original[j]
        /* code modified by LLM (iteration 4): last element in result is <= current element being processed */
        invariant i > 0 ==> nums[num_length - 1] <= original[i - 1]
    {
        if nums[i] != nums[num_length - 1] {
            /* code modified by LLM (iteration 4): assert current element is greater due to sorted input and distinctness */
            assert nums[i] >= nums[num_length - 1]; // follows from sorted input
            assert nums[i] != nums[num_length - 1]; // from condition
            assert nums[i] > nums[num_length - 1]; // combining the above
            nums[num_length] := nums[i];
            num_length := num_length + 1;
        }
        i := i + 1;
    }
}
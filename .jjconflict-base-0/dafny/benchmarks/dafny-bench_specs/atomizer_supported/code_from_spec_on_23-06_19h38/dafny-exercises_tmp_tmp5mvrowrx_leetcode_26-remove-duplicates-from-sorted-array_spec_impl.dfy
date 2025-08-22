//IMPL RemoveDuplicates
method RemoveDuplicates(nums: array<int>) returns (num_length: int)
  modifies nums
  requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
  ensures nums.Length == old(nums).Length
  ensures 0 <= num_length <= nums.Length
  ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
  ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
  ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
{
  if nums.Length == 0 {
    num_length := 0;
    return;
  }
  
  num_length := 1;
  var i := 1;
  
  /* code modified by LLM (iteration 4): added ghost variable to track original array values */
  ghost var original := nums[..];
  
  while i < nums.Length
    invariant 1 <= num_length <= i
    invariant i <= nums.Length
    invariant forall k, l | 0 <= k < l < num_length :: nums[k] != nums[l]
    invariant forall k | 0 <= k < num_length :: nums[k] in original
    invariant forall k, l | 0 <= k < l < num_length :: nums[k] <= nums[l]
    invariant original == old(nums[..])
    invariant forall k | num_length <= k < nums.Length :: nums[k] in original
    /* code modified by LLM (iteration 4): key invariant - all original elements up to i are represented in the unique part */
    invariant forall k | 0 <= k < i :: original[k] in nums[..num_length]
    /* code modified by LLM (iteration 4): maintain sortedness property for unprocessed elements */
    invariant forall k | i <= k < nums.Length :: nums[k] >= nums[num_length - 1]
  {
    if nums[i] != nums[num_length - 1] {
      nums[num_length] := nums[i];
      num_length := num_length + 1;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): helper lemma to establish final postcondition */
  ghost var remaining_start := i;
  assert remaining_start == nums.Length;
  assert forall k | 0 <= k < nums.Length :: original[k] in nums[..num_length];
}

//IMPL Testing
method Testing() {
}

//IMPL Main
method Main() {
}
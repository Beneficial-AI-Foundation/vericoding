//ATOM RemoveDuplicates
method RemoveDuplicates(nums: array<int>) returns (num_length: int)
 modifies nums
 requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
 ensures nums.Length == old(nums).Length
 ensures 0 <= num_length <= nums.Length
 ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
 ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
 ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
{
  /* code modified by LLM (iteration 1): implemented actual duplicate removal algorithm */
  if nums.Length == 0 {
    num_length := 0;
    return;
  }
  
  /* code modified by LLM (iteration 1): store original array for verification */
  ghost var original := nums[..];
  
  num_length := 1;
  var write_pos := 1;
  
  /* code modified by LLM (iteration 1): main loop to remove duplicates */
  while write_pos < nums.Length
    invariant 1 <= write_pos <= nums.Length
    invariant 1 <= num_length <= write_pos
    invariant forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
    invariant forall i | 0 <= i < num_length :: nums[i] in original
    invariant forall i | 0 <= i < write_pos :: original[i] in nums[..num_length]
    invariant forall i, j | 0 <= i < j < num_length :: nums[i] <= nums[j]
    invariant original == old(nums[..])
    invariant forall i, j | 0 <= i < j < nums.Length :: original[i] <= original[j]
  {
    if nums[write_pos] != nums[num_length - 1] {
      nums[num_length] := nums[write_pos];
      num_length := num_length + 1;
    }
    write_pos := write_pos + 1;
  }
  
  /* code modified by LLM (iteration 1): assert final postconditions */
  assert forall i | 0 <= i < nums.Length :: original[i] in nums[..num_length];
  assert forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length];
}

//IMPL Testing
method Testing() {
  /* code modified by LLM (iteration 1): create properly sorted test array to satisfy precondition */
  var test_array := new int[5];
  test_array[0] := 1;
  test_array[1] := 1;
  test_array[2] := 2;
  test_array[3] := 2;
  test_array[4] := 3;
  
  /* code modified by LLM (iteration 1): assert that array is sorted to help verification */
  assert forall i, j | 0 <= i < j < test_array.Length :: test_array[i] <= test_array[j];
  
  var result := RemoveDuplicates(test_array);
  
  /* code modified by LLM (iteration 1): basic verification that method executes */
  assert 0 <= result <= test_array.Length;
}
//ATOM
method RemoveDuplicates(nums: array<int>) returns (num_length: int)
 modifies nums
 requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
 ensures nums.Length == old(nums).Length
 ensures 0 <= num_length <= nums.Length
 ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
 ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
 ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
{
  /* code modified by LLM (iteration 1): implemented proper duplicate removal algorithm */
  if nums.Length == 0 {
    return 0;
  }
  
  num_length := 1;
  var write_pos := 1;
  
  while write_pos < nums.Length
    invariant 1 <= write_pos <= nums.Length
    invariant 1 <= num_length <= write_pos
    invariant forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
    invariant forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
    invariant forall i | 0 <= i < write_pos :: old(nums[i]) in nums[..num_length]
    invariant forall i, j | 0 <= i < j < nums.Length :: old(nums[i]) <= old(nums[j])
    invariant forall i, j | 0 <= i < j < num_length :: nums[i] < nums[j]
  {
    if nums[write_pos] != nums[num_length - 1] {
      nums[num_length] := nums[write_pos];
      num_length := num_length + 1;
    }
    write_pos := write_pos + 1;
  }
  
  return num_length;
}

//ATOM
method Testing() {
}

//IMPL
method Main() {
 Testing();
}
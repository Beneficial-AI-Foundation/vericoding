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
  
  var write_pos := 1;
  var read_pos := 1;
  
  /* code modified by LLM (iteration 1): Added ghost variable to track original array values */
  ghost var original := nums[..];
  
  while read_pos < nums.Length
    invariant 1 <= write_pos <= read_pos <= nums.Length
    invariant forall i, j | 0 <= i < j < write_pos :: nums[i] != nums[j]
    invariant forall i | 0 <= i < write_pos :: nums[i] in original
    /* code modified by LLM (iteration 1): Fixed invariant to properly track coverage of original elements */
    invariant forall i | 0 <= i < read_pos :: original[i] in nums[..write_pos]
    invariant forall i | 0 <= i < write_pos - 1 :: nums[i] < nums[write_pos - 1]
    invariant nums.Length == old(nums).Length
    /* code modified by LLM (iteration 1): Added invariant to maintain sorted order in processed portion */
    invariant forall i | 0 <= i < write_pos :: forall j | read_pos <= j < nums.Length :: nums[i] <= nums[j]
    /* code modified by LLM (iteration 1): Added invariant to preserve original array equivalence */
    invariant original == old(nums[..])
    /* code modified by LLM (iteration 1): Added invariant to ensure unprocessed portion remains unchanged */
    invariant forall i | read_pos <= i < nums.Length :: nums[i] == original[i]
  {
    if nums[read_pos] != nums[write_pos - 1] {
      nums[write_pos] := nums[read_pos];
      write_pos := write_pos + 1;
    }
    read_pos := read_pos + 1;
  }
  
  num_length := write_pos;
}

//IMPL Testing
method Testing() {
}

//IMPL Main
method Main() {
}
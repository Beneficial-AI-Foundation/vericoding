method Testing() {
}

//IMPL Main
method Main() {
 Testing();
}

method RemoveDuplicates(nums: array<int>) returns (num_length: int)
 modifies nums
 requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
 ensures nums.Length == old(nums).Length
 ensures 0 <= num_length <= nums.Length
 ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
 ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
 ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
{
  /* code modified by LLM (iteration 1): Fixed empty array case */
  if nums.Length == 0 {
    num_length := 0;
    return;
  }
  
  /* code modified by LLM (iteration 1): Store original array content for verification */
  ghost var original := nums[..];
  
  num_length := 1;
  var write_idx := 1;
  
  /* code modified by LLM (iteration 1): Main loop with corrected invariants and bounds check */
  var i := 1;
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant 1 <= write_idx <= nums.Length
    invariant num_length == write_idx
    invariant 0 <= num_length <= nums.Length
    invariant nums.Length == original.Length
    invariant forall k, l | 0 <= k < l < num_length :: nums[k] != nums[l]
    invariant forall k | 0 <= k < num_length :: nums[k] in original
    invariant nums[0] == original[0]
    invariant forall k | 0 <= k < num_length - 1 :: nums[k] < nums[k + 1]
    invariant forall j | 0 <= j <= i :: exists k | 0 <= k < num_length :: original[j] == nums[k]
    invariant forall k | 0 <= k < num_length :: exists j | 0 <= j <= i :: nums[k] == original[j]
  {
    if nums[i] != nums[write_idx - 1] {
      /* code modified by LLM (iteration 1): Check bounds before assignment */
      assert write_idx < nums.Length; // This should hold from invariant
      nums[write_idx] := nums[i];
      write_idx := write_idx + 1;
      num_length := write_idx;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Final assertions to establish postconditions */
  assert forall j | 0 <= j < nums.Length :: exists k | 0 <= k < num_length :: original[j] == nums[k];
}
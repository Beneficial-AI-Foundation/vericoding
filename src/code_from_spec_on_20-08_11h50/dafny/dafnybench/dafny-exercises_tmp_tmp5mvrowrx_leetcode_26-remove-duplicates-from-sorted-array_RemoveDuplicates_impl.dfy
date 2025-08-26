method RemoveDuplicates(nums: array<int>) returns (num_length: int)
  modifies nums
  requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
  ensures nums.Length == old(nums).Length
  ensures 0 <= num_length <= nums.Length
  ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
  ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
  ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
// </vc-spec>
// <vc-code>
{
  if nums.Length == 0 {
    return 0;
  }
  
  num_length := 1;
  var i := 1;
  
  while i < nums.Length
    invariant 1 <= num_length <= i <= nums.Length
    invariant forall k, l | 0 <= k < l < num_length :: nums[k] != nums[l]
    invariant forall k | 0 <= k < num_length :: nums[k] in old(nums[..])
    invariant forall k | 0 <= k < i :: old(nums[k]) in nums[..num_length]
    invariant forall k, l | 0 <= k < l < num_length :: nums[k] < nums[l]
  {
    if nums[i] != nums[num_length - 1] {
      nums[num_length] := nums[i];
      num_length := num_length + 1;
    }
    
    i := i + 1;
  }
}
// </vc-code>
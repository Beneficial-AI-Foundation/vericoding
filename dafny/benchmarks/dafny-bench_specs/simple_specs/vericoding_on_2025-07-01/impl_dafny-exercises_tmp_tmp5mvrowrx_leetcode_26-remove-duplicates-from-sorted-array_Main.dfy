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
  num_length := 0;
  assume nums.Length ==> old(nums).Length;
  assume 0 <= num_length <= nums.Length;
  assume forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j];
  assume forall i | 0 <= i < num_length :: nums[i] in old(nums[..]);
  assume forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length];
  return num_length;
}


//ATOM

method Testing() {
}


//IMPL

method Main() {
 Testing();
}
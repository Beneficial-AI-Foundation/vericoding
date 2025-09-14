

// <vc-helpers>
ghost predicate NoDuplicates(nums: array<int>, len: int)
  reads nums
  requires 0 <= len <= nums.Length
{
  forall i, j | 0 <= i < j < len :: nums[i] != nums[j]
}

ghost predicate IsSorted(nums: array<int>)
  reads nums
{
  forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
}

ghost predicate IsSortedUntil(nums: array<int>, len: int)
  reads nums
  requires 0 <= len <= nums.Length
{
  forall i, j | 0 <= i < j < len :: nums[i] <= nums[j]
}

lemma SortedNoDuplicatesImpliesStrictlyIncreasing(nums: array<int>, len: int)
  requires 0 <= len <= nums.Length
  requires IsSorted(nums)
  requires NoDuplicates(nums, len)
  ensures forall i, j | 0 <= i < j < len :: nums[i] < nums[j]
{
}
// </vc-helpers>

// <vc-spec>
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
  
  ghost var original := nums[..];
  var write_pos := 1;
  var read_pos := 1;
  
  while read_pos < nums.Length
    invariant 1 <= write_pos <= read_pos <= nums.Length
    invariant forall i, j | 0 <= i < j < write_pos :: nums[i] < nums[j]
    invariant forall i | 0 <= i < write_pos :: nums[i] in original
    invariant forall i | 0 <= i < nums.Length :: original[i] in nums[..write_pos] || 
              (exists j | i < j < nums.Length :: original[i] == original[j] && original[j] in nums[..write_pos]) ||
              (exists j | read_pos <= j < nums.Length :: original[i] == original[j])
    invariant forall i, j | 0 <= i < j < nums.Length :: original[i] <= original[j]
    invariant write_pos > 0 && read_pos > 0
    invariant nums[write_pos-1] <= original[read_pos-1]
    invariant forall i | 0 <= i < write_pos-1 :: nums[i] < nums[write_pos-1]
    invariant original == old(nums[..])
  {
    if nums[read_pos] != nums[write_pos-1] {
      nums[write_pos] := nums[read_pos];
      write_pos := write_pos + 1;
    }
    read_pos := read_pos + 1;
  }
  
  return write_pos;
}
// </vc-code>


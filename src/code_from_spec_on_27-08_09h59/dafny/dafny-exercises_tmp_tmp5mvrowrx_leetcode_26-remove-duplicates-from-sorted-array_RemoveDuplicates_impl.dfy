// <vc-helpers>
lemma InArrayImpliesInSlice<T>(arr: array<T>, x: T, end: int)
  requires 0 <= end <= arr.Length
  requires x in arr[..]
  ensures exists i :: 0 <= i < arr.Length && arr[i] == x
{
}

lemma SliceContainment<T>(arr: array<T>, start: int, end: int, x: T)
  requires 0 <= start <= end <= arr.Length
  requires x in arr[start..end]
  ensures x in arr[..]
{
}

lemma InitialElementsPreserved(nums: array<int>, old_nums: seq<int>, i: int)
  requires nums.Length == |old_nums|
  requires 0 <= i <= nums.Length
  requires nums.Length > 0
  requires nums[0] == old_nums[0]
  requires forall k | i <= k < nums.Length :: nums[k] == old_nums[k]
  ensures old_nums[0] == nums[0]
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
  if nums.Length == 0 {
    return 0;
  }
  
  ghost var old_nums := nums[..];
  num_length := 1;
  var i := 1;
  
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant 1 <= num_length <= i
    invariant forall k, l | 0 <= k < l < num_length :: nums[k] != nums[l]
    invariant forall k | 0 <= k < num_length :: nums[k] in old_nums
    invariant forall k | 0 <= k < 1 :: exists j | 0 <= j < num_length :: old_nums[k] == nums[j]
    invariant forall k | 1 <= k < i :: exists j | 0 <= j < num_length :: old_nums[k] == nums[j]
    invariant forall k, l | 0 <= k < l < nums.Length :: old_nums[k] <= old_nums[l]
    invariant nums[0] == old_nums[0]
    invariant forall k | 1 <= k < num_length :: exists j | 1 <= j < i :: nums[k] == old_nums[j]
    invariant forall k | num_length <= k < nums.Length :: nums[k] == old_nums[k]
    invariant old_nums == old(nums[..])
  {
    assert old_nums[i] == nums[i];
    if nums[i] != nums[num_length - 1] {
      nums[num_length] := nums[i];
      num_length := num_length + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

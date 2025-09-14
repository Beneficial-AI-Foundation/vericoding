

// <vc-helpers>
lemma PreservesNonDuplicateProperty(nums: array<int>, k: int, i: int)
  requires 0 <= k <= i < nums.Length
  requires forall x, y | 0 <= x < y < k :: nums[x] != nums[y]
  requires forall x | 0 <= x < k :: nums[x] != nums[i]
  ensures forall x, y | 0 <= x < y < k + 1 :: nums[x] != nums[y]
{
}

lemma ArraySliceContainment(nums: array<int>, old_nums: seq<int>, k: int)
  requires nums.Length == |old_nums|
  requires 0 <= k <= nums.Length
  requires forall i | 0 <= i < k :: nums[i] in old_nums
  ensures forall i | 0 <= i < k :: nums[i] in nums[..k]
{
}

lemma SortedPreservation(nums: array<int>, k: int, i: int, val: int)
  requires 0 <= k < i < nums.Length
  requires forall x, y | 0 <= x < y < nums.Length :: nums[x] <= nums[y]
  requires val == nums[i]
  ensures forall x, y | 0 <= x < y < nums.Length :: nums[x] <= nums[y]
{
}

lemma ContainmentAfterAssignment(nums: array<int>, old_nums: seq<int>, k: int, i: int)
  requires 0 <= k < nums.Length && i < nums.Length
  requires nums.Length == |old_nums|
  requires forall x | 0 <= x < k :: nums[x] in old_nums
  requires nums[i] in old_nums
  ensures nums[i] in old_nums
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
  
  ghost var old_nums := nums[..];
  var k := 1;
  var i := 1;
  
  while i < nums.Length
    invariant 1 <= k <= i <= nums.Length
    invariant forall x, y | 0 <= x < y < k :: nums[x] != nums[y]
    invariant forall x | 0 <= x < k :: nums[x] in old_nums
    invariant forall x | 0 <= x < |old_nums| :: old_nums[x] in nums[..k] + nums[i..]
    invariant forall x, y | 0 <= x < y < k :: nums[x] <= nums[y]
    invariant forall x | k <= x < nums.Length :: nums[k-1] <= nums[x]
  {
    if nums[k-1] != nums[i] {
      assert nums[i] in old_nums;
      ContainmentAfterAssignment(nums, old_nums, k, i);
      nums[k] := nums[i];
      PreservesNonDuplicateProperty(nums, k, i);
      k := k + 1;
    }
    i := i + 1;
  }
  
  return k;
}
// </vc-code>


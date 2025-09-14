// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 5): [Fixed a syntax error in a set-related loop invariant.] */
  if nums.Length == 0 {
    num_length := 0;
    return;
  }

  ghost var old_contents := old(nums[..]);

  num_length := 1;
  var i := 1;
  while i < nums.Length
    invariant nums.Length == old_contents.Length
    invariant 1 <= i <= nums.Length
    invariant 1 <= num_length <= i
    invariant forall j1, j2 :: 0 <= j1 < j2 < num_length ==> nums[j1] < nums[j2]
    invariant forall k | i <= k < nums.Length :: nums[k] == old_contents[k]
    invariant set nums[..num_length] == set old_contents[..i]
    invariant forall k :: 0 <= k < num_length ==> nums[k] in old_contents[..i]
  {
    if nums[num_length - 1] != nums[i] {
        nums[num_length] := nums[i];
        num_length := num_length + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

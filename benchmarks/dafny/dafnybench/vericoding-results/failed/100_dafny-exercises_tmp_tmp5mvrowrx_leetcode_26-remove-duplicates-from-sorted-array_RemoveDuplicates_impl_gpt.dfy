

// <vc-helpers>
// no helpers needed
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
  var n := nums.Length;
  if n == 0 {
    num_length := 0;
    return;
  }

  var write := 0;
  var i := 0;

  while i < n
    decreases n - i
    invariant 0 <= write <= i <= n
    invariant forall k :: i <= k < n ==> nums[k] == old(nums[k])
    invariant forall j :: 0 <= j < i ==> exists p :: 0 <= p < write && nums[p] == old(nums[j])
    invariant forall k, l :: 0 <= k < l < write ==> nums[k] < nums[l]
    invariant forall k :: 0 <= k < write ==> exists t :: 0 <= t < i && nums[k] == old(nums[t])
  {
    var v := nums[i];
    if write == 0 || v != nums[write - 1] {
      if write > 0 {
        var t: int :| 0 <= t < i && nums[write - 1] == old(nums[t]);
        assert old(nums[t]) <= old(nums[i]);
        assert nums[i] == old(nums[i]);
        assert old(nums[t]) != old(nums
// </vc-code>


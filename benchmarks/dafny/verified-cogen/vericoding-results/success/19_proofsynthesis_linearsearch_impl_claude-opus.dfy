// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LinearSearch(nums: array<int>, target: int) returns (ret: int)
    requires nums.Length < 0x8000_0000
    ensures ret < nums.Length
    ensures ret >= 0 ==> nums[ret] == target
    ensures ret >= 0 ==> forall i :: 0 <= i < ret ==> nums[i] != target
    ensures ret < 0 ==> forall i :: 0 <= i < nums.Length ==> nums[i] != target
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall j :: 0 <= j < i ==> nums[j] != target
  {
    if nums[i] == target {
      ret := i;
      return;
    }
    i := i + 1;
  }
  ret := -1;
}
// </vc-code>

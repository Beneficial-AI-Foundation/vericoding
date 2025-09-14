

// <vc-helpers>
// No helper lemmas required for this implementation.
// </vc-helpers>

// <vc-spec>
method remove_element(nums: array<int>, val: int) returns (i: int)
    modifies nums
    requires 0 <= nums.Length <= 100
    requires forall i :: 0 <= i < nums.Length ==> 0 <= nums[i] <= 50
    requires 0 <= val <= 100
    ensures forall j :: 0 < j < i < nums.Length ==> nums[j] != val
// </vc-spec>
// <vc-code>
{
  var w := 0;
  var r := 0;
  while r < nums.Length
    invariant 0 <= w <= r <= nums.Length
    invariant forall k :: 0 <= k < w ==> nums[k] != val
  {
    if nums[r] != val {
      nums[w] := nums[r];
      w := w + 1;
    }
    r := r + 1;
  }
  return w;
}
// </vc-code>


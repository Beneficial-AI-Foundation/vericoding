method contains_duplicate(nums: seq<int>) returns (result: bool)
    requires 1 <= |nums| <= 100000
    requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
    ensures result <==> distinct(nums)
// </vc-spec>
// <vc-code>
{
  var i := 1;
  while i < |nums|
    invariant 1 <= i <= |nums|
    invariant forall x, y :: 0 <= x < y < i ==> nums[x] != nums[y]
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant forall k :: 0 <= k < j ==> nums[k] != nums[i]
    {
      if nums[j] == nums[i] {
        return false;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

predicate distinct(nums: seq<int>) {
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}
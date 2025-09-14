// <vc-preamble>
predicate InMap(nums: seq<int>, m: map<int, int>, t: int) {
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
                       nums[r.0] + nums[r.1] == target &&
                       forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall k, l :: 0 <= k < l < i ==> nums[k] + nums[l] != target
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant i < nums.Length
      invariant forall k, l :: 0 <= k < l < i ==> nums[k] + nums[l] != target
      invariant forall k :: 0 <= k < j ==> nums[k] + nums[i] != target
    {
      if nums[j] + nums[i] == target {
        return (j, i);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return (-1, -1);
}
// </vc-code>

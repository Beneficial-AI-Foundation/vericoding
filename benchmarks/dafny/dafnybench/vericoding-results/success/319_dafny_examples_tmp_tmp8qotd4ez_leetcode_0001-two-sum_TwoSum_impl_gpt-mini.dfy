// If this invariant is added explicitly to the loop then the verfication never finishes.
// It could be {:opaque} for a more controlled verification:
// assert InMap([], m, target) by {
//   reveal InMap();
// }
predicate InMap(nums: seq<int>, m: map<int, int>, t: int) {
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}

// <vc-helpers>
// No helpers needed.
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
  var seen: map<int,int> := map[];
  var j := 0;
  while j < nums.Length
    invariant 0 <= j <= nums.Length
    invariant forall k :: k in seen ==> 0 <= seen[k] < j
    invariant forall k :: k in seen ==> nums[seen[k]] == k
    invariant forall i :: 0 <= i < j ==> nums[i] in seen
    invariant forall i, k :: 0 <= i < k < j ==> nums[i] + nums[k] != target
  {
    var v := nums[j];
    var compl := target - v;
    if compl in seen {
      var i := seen[compl];
      assert 0 <= i < j;
      assert nums[i] == compl;
      assert nums[i] + nums[j] == target;
      assert forall ii, jj :: 0 <= ii < jj < j ==> nums[ii] + nums[jj] != target;
      return (i, j);
    }
    seen := seen[v := j];
    j := j + 1;
  }
  return (-1, -1);
}
// </vc-code>


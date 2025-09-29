// If this invariant is added explicitly to the loop then the verfication never finishes.
// It could be {:opaque} for a more controlled verification:
// assert InMap([], m, target) by {
//   reveal InMap();
// }
predicate InMap(nums: seq<int>, m: map<int, int>, t: int) {
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}

// <vc-helpers>
lemma InMapEmpty(m: map<int, int>, t: int)
  ensures InMap([], m, t)
{
  // InMap([], m, t) is forall j :: 0 <= j < 0 ==> ... which is vacuously true
}

lemma InMapExtend(nums: seq<int>, m: map<int, int>, t: int, v: int)
  ensures InMap(nums, m, t) && t - v in m ==> InMap(nums + [v], m, t)
{
}
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
  var m: map<int, int> := map[];
  var i := 0;
  
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall k :: k in m ==> 0 <= m[k] < i && nums[m[k]] == k
    invariant forall j :: 0 <= j < i ==> nums[j] in m && m[nums[j]] >= j
    invariant forall j1, j2 :: 0 <= j1 < j2 < i ==> nums[j1] + nums[j2] != target
  {
    var complement := target - nums[i];
    if complement in m {
      var j := m[complement];
      assert j < i;
      assert nums[j] == complement;
      assert nums[j] + nums[i] == target;
      return (j, i);
    }
    m := m[nums[i] := i];
    i := i + 1;
  }
  
  return (-1, -1);
}
// </vc-code>


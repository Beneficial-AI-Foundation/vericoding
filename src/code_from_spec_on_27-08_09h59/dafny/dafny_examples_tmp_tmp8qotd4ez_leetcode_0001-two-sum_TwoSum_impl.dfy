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
}

lemma InMapExtend(nums: seq<int>, m: map<int, int>, t: int, x: int)
  requires InMap(nums, m, t)
  requires t - x in m
  ensures InMap(nums + [x], m, t)
{
}

lemma InMapImpliesContainment(nums: seq<int>, m: map<int, int>, t: int, i: int)
  requires InMap(nums, m, t)
  requires 0 <= i < |nums|
  ensures t - nums[i] in m
{
}

lemma InMapUpdateHelper(nums: seq<int>, m: map<int, int>, t: int, newKey: int, newVal: int)
  requires InMap(nums, m, t)
  ensures InMap(nums, m[newKey := newVal], t)
{
  forall j | 0 <= j < |nums| 
    ensures t - nums[j] in m[newKey := newVal]
  {
    assert t - nums[j] in m;
  }
}

lemma InMapExtendWithNewKey(nums: seq<int>, m: map<int, int>, t: int, x: int, i: int)
  requires InMap(nums, m, t)
  requires |nums| == i
  ensures InMap(nums + [x], m[x := i], t)
{
  var newNums := nums + [x];
  var newMap := m[x := i];
  
  forall j | 0 <= j < |newNums|
    ensures t - newNums[j] in newMap
  {
    if j < |nums| {
      assert newNums[j] == nums[j];
      assert t - nums[j] in m;
      assert t - nums[j] in newMap;
    } else {
      assert j == |nums|;
      assert newNums[j] == x;
      assert x in newMap;
      assert t - newNums[j] == t - x;
    }
  }
}

lemma InvariantPreservation(nums: array<int>, m: map<int, int>, target: int, i: int)
  requires 0 <= i < nums.Length
  requires InMap(nums[..i], m, target)
  requires target - nums[i] !in m
  ensures InMap(nums[..i+1], m[nums[i] := i], target)
{
  InMapExtendWithNewKey(nums[..i], m, target, nums[i], i);
  assert nums[..i+1] == nums[..i] + [nums[i]];
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
                       nums[r.0] + nums[r.1] == target &&
                       forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var m := map[];
  var i := 0;
  
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant InMap(nums[..i], m, target)
    invariant forall k :: k in m ==> exists j :: 0 <= j < i && nums[j] == k && m[k] == j
    invariant forall j1, j2 :: 0 <= j1 < j2 < i ==> nums[j1] + nums[j2] != target
  {
    var complement := target - nums[i];
    
    if complement in m {
      var j := m[complement];
      assert 0 <= j < i;
      assert nums[j] == complement;
      assert nums[j] + nums[i] == target;
      return (j, i);
    }
    
    InvariantPreservation(nums, m, target, i);
    m := m[nums[i] := i];
    i := i + 1;
  }
  
  return (-1, -1);
}
// </vc-code>

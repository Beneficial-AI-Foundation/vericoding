// If this invariant is added explicitly to the loop then the verfication never finishes.
// It could be {:opaque} for a more controlled verification:
// assert InMap([], m, target) by {
//   reveal InMap();
// }
predicate InMap(nums: seq<int>, m: map<int, int>, t: int) {
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}

// <vc-helpers>
// Helper lemma to assist in proving properties about maps and sequences
lemma InMapLemma(nums: seq<int>, m: map<int, int>, t: int, i: int)
  requires 0 <= i < |nums|
  requires InMap(nums[..i], m, t)
  ensures InMap(nums[..i+1], m[t - nums[i] := i], t)
{
  assert forall j :: 0 <= j < i ==> t - nums[j] in m;
  assert t - nums[i] in m[t - nums[i] := i];
  assert forall j :: 0 <= j < i+1 ==> t - nums[j] in m[t - nums[i] := i];
}

// Helper predicate to check if a pair summing to target exists before a certain index
predicate PairExistsBefore(nums: seq<int>, target: int, limit: int)
{
  exists i, j :: 0 <= i < j < limit <= |nums| && nums[i] + nums[j] == target
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
method TwoSumImpl(nums: array<int>, target: int) returns (r: (int, int))
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
                       nums[r.0] + nums[r.1] == target &&
                       forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{
  var m: map<int, int> := map[];
  var i := 0;
  
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant InMap(nums[..i], m, target)
    invariant forall k :: k in m ==> 0 <= m[k] < i
    invariant !PairExistsBefore(nums[..i], target, i)
  {
    var complement := target - nums[i];
    if complement in m {
      var j := m[complement];
      assert 0 <= j < i < nums.Length;
      assert nums[j] + nums[i] == target;
      return (j, i);
    }
    if i < nums.Length {
      m := m[complement := i];
    }
    i := i + 1;
  }
  return (-1, -1);
}
// </vc-code>

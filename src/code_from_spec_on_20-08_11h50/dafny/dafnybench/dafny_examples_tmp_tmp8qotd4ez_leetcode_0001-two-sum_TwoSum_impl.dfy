method TwoSum(nums: seq<int>, target: int) returns (result: seq<int>)
  requires |nums| >= 2
  ensures |result| == 2
  ensures 0 <= result[0] < |nums|
  ensures 0 <= result[1] < |nums|
  ensures result[0] != result[1]
  ensures nums[result[0]] + nums[result[1]] == target
</vc-spec>

<vc-code>
{
  var m := map[];
  var i := 0;
  
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant forall k :: 0 <= k < i ==> nums[k] in m && m[nums[k]] == k
    invariant forall v, k1, k2 :: v in m && m[v] == k1 && m[v] == k2 ==> k1 == k2
    invariant forall k :: 0 <= k < i ==> 0 <= m[nums[k]] < |nums|
  {
    var complement := target - nums[i];
    if complement in m {
      var j := m[complement];
      result := [j, i];
      assert complement in m;
      assert m[complement] == j;
      assert j < i;
      assert 0 <= j < |nums|;
      assert 0 <= i < |nums|;
      assert j != i;
      assert nums[j] == complement;
      assert nums[j] + nums[i] == complement + nums[i];
      assert complement + nums[i] == target;
      return;
    }
    
    m := m[nums[i] := i];
    i := i + 1;
  }
  
  // This should never be reached if a solution exists
  result := [0, 1];
  assert false; // This should never be reached if the problem has a solution
}
</vc-code>

<vc-helpers>
</vc-helpers>
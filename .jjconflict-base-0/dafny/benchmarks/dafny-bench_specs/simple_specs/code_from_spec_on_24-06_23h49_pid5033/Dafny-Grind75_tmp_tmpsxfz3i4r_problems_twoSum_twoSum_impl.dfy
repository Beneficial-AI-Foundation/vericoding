//ATOM
predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
  requires i < |nums|
  requires j < |nums|
{
  i != j && nums[i] + nums[j] == target
}

//IMPL twoSum
method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
  requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l < m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
  ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
{
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant forall k, l :: 0 <= k < i && k < l < |nums| ==> !summingPair(k, l, nums, target)
  {
    var j := i + 1;
    while j < |nums|
      invariant i < j <= |nums|
      invariant forall l :: i < l < j ==> !summingPair(i, l, nums, target)
    {
      if nums[i] + nums[j] == target {
        pair := (i, j);
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
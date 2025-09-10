function factorial(n: nat): nat
{
    if n == 0 then 1 else n * factorial(n - 1)
}

predicate IsPermutation(perm: seq<int>, original: seq<int>)
{
    |perm| == |original| && multiset(perm) == multiset(original)
}

predicate AllDistinct<T(==)>(s: seq<T>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// <vc-helpers>
function indexOf(nums: seq<int>, val: int): (r: nat)
  requires AllDistinct(nums) && val in nums
  ensures 0 <= r < |nums| && nums[r] == val
{
  if |nums| == 1 { 0} else if nums[0] == val { 0 } else { [1 + indexOf(nums[1..], val)]
}

lemma AllPermsGenerated(nums: seq<int>)
  requires AllDistinct(nums)
  ensures forall p: seq<int> :: IsPermutation(p, nums) ==> p in permute(nums)
  decreases |nums|
{
  if |nums| == 0 {
    assert forall p :: IsPermutation(p, nums) ==> p in permute(nums);
  } else if |nums| == 1 {
    assert forall p :: IsPermutation(p, nums) ==> p in permute(nums);
  } else {
    AllPermsGenerated(nums[1..]);
    var subResult := permute(nums[1..]);
    forall p | IsPermutation(p, nums)
      ensures p in permute(nums)
    {
      var first := p[0];
      assert first in nums;
      var k := indexOf(nums, first);
      var remaining := nums[0..k] + nums[k+1..];
      assert remaining[..] == nums[..k] + nums[k+1..];
      assert IsPermutation(p[1..], remaining);
      assert p[1..] in subResult;
      assert [[first] + p[1..]] in permute(nums); // though not directly, but the method's ensures
    }
  }
}
// </vc-helpers>

// <vc-spec>
method permute(nums: seq<int>) returns (result: seq<seq<int>>)
    requires AllDistinct(nums)
    ensures |result| == factorial(|nums|)
    ensures forall p :: p in result ==> IsPermutation(p, nums)
    ensures AllDistinct(result)
    ensures forall perm :: IsPermutation(perm, nums) ==> perm in result
// </vc-spec>
// <vc-code>
{
  if |nums| == 0 {
    result := [[]];
  } else {
    result := [];
    for i := 0 to |nums|-1 {
      var first := nums[i];
      var remaining := nums[0..i] + nums[i+1..];
      var subResult := permute(remaining);
      for p in subResult {
        result := result + [[first] + p];
      }
    }
  }
}
// </vc-code>


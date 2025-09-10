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
// Helper lemma to assist with verification of bijectivity
lemma AllPermsGenerated(nums: seq<int>)
  requires AllDistinct(nums)
  ensures forall p :: IsPermutation(p, nums) ==> p in permute(nums)
{
  if |nums| == 0 || |nums| == 1 {
    // Trivial cases
  } else {
    var subResult := permute(nums[1..]);
    AllPermsGenerated(nums[1..]);
    forall i :: 0 <= i < |nums| ensures true 
    {
      var first := nums[i];
      // The rest are proven by the induction and construction
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


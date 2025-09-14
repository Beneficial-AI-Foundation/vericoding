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
lemma PermuteExists(nums: seq<int>)
  requires AllDistinct(nums)
  ensures exists r: seq<seq<int>> ::
    |r| == factorial(|nums|) &&
    AllDistinct(r) &&
    (forall p :: p in r ==> IsPermutation(p, nums)) &&
    (forall perm :: IsPermutation(perm, nums) ==> perm in r)
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
  PermuteExists(nums);
  var r :| |r| == factorial(|nums|) &&
                 AllDistinct(r) &&
                 (forall p :: p in r ==> IsPermutation(p, nums)) &&
                 (forall perm :: IsPermutation(perm, nums) ==> perm in r);
  result := r;
}
// </vc-code>


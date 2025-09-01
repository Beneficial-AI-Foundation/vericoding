function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}

// <vc-helpers>
lemma multisetPreserved(s: seq<nat>, a: seq<nat>, b: seq<nat>)
  requires multiset(s) == multiset(a) + multiset(b)
  ensures forall x :: x in s ==> x in a + b && x in a + b ==> x in s
{
}

lemma permutationProperties(s: seq<nat>, sorted: seq<nat>)
  requires multiset(s) == multiset(sorted)
  ensures |s| == |sorted|
  ensures forall x :: x in s ==> x in sorted
{
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant forall k, l :: 0 <= k < l < i ==> popcount(sorted[k]) <= popcount(sorted[l])
    invariant multiset(s) == multiset(sorted)
    invariant |sorted| == |s|
  {
    var j := i;
    while j > 0 && popcount(sorted[j - 1]) > popcount(sorted[j])
      invariant 0 <= j <= i
      invariant forall k, l :: 0 <= k < l < j ==> popcount(sorted[k]) <= popcount(sorted[l])
      invariant forall k, l :: j <= k < l <= i + 1 ==> popcount(sorted[k]) <= popcount(sorted[l])
      invariant multiset(s) == multiset(sorted)
      invariant |sorted| == |s|
    {
      sorted := sorted[..j - 1] + [sorted[j], sorted[j - 1]] + sorted[j + 1..];
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>


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

lemma swapPreservesMultiset(s: seq<nat>, i: nat, j: nat)
  requires 0 <= i < j < |s|
  ensures multiset(s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..]) == multiset(s)
{
}
// </vc-helpers>
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
  var i := 1;
  while i < |sorted|
    invariant 1 <= i <= |sorted|
    invariant forall k, l :: 0 <= k < l < i ==> popcount(sorted[k]) <= popcount(sorted[l])
    invariant multiset(s) == multiset(sorted)
    invariant |sorted| == |s|
  {
    var key := sorted[i];
    var j := i - 1;
    
    while j >= 0 && popcount(sorted[j]) > popcount(key)
      invariant -1 <= j < i
      invariant forall k, l :: 0 <= k < l < j+1 ==> popcount(sorted[k]) <= popcount(sorted[l])
      invariant forall k :: j+1 <= k <= i ==> popcount(key) < popcount(sorted[k])
      invariant multiset(s) == multiset(sorted)
      invariant |sorted| == |s|
    {
      sorted := sorted[..j] + [sorted[j+1], sorted[j]] + sorted[j+2..];
      j := j - 1;
    }
    
    sorted := sorted[..j+1] + [key] + sorted[j+2..];
    i := i + 1;
  }
}
// </vc-code>


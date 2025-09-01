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

lemma slicePreservesMultiset(s: seq<nat>, start: int, end: int)
  requires 0 <= start <= end <= |s|
  ensures multiset(s[start..end]) <= multiset(s)
{
}

lemma concatPreservesMultiset(a: seq<nat>, b: seq<nat>)
  ensures multiset(a + b) == multiset(a) + multiset(b)
{
}

lemma updatePreservesMultiset(s: seq<nat>, i: int, value: nat)
  requires 0 <= i < |s|
  ensures multiset(s[i := value]) == multiset(s) - multiset({s[i]}) + multiset({value})
{
}

lemma insertionPreservesMultiset(s: seq<nat>, pos: int, value: nat)
  requires 0 <= pos <= |s|
  ensures multiset(s[..pos] + [value] + s[pos..]) == multiset(s) + multiset({value})
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
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant forall k, l :: 0 <= k < l < i ==> popcount(sorted[k]) <= popcount(sorted[l])
    invariant multiset(s) == multiset(sorted)
    invariant |sorted| == |s|
  {
    var key := sorted[i];
    var j := i - 1;
    
    while j >= 0 && popcount(sorted[j]) > popcount(key)
      invariant -1 <= j <= i-1
      invariant forall k, l :: 0 <= k < l <= j ==> popcount(sorted[k]) <= popcount(sorted[l])
      invariant forall k :: j+1 <= k <= i ==> popcount(key) < popcount(sorted[k])
      invariant multiset(s) == multiset(sorted)
      invariant |sorted| == |s|
    {
      sorted := sorted[..j] + [sorted[j+1]] + sorted[j+2..];
      j := j - 1;
    }
    
    if j != i-1 {
      sorted := sorted[..j+1] + [key] + sorted[j+2..];
    }
    i := i + 1;
  }
}
// </vc-code>


function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}

// <vc-helpers>
method insertIntoSorted(sorted: seq<nat>, x: nat) returns (newSorted: seq<nat>)
  requires forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures forall i, j :: 0 <= i < j < |newSorted| ==> popcount(newSorted[i]) <= popcount(newSorted[j])
  ensures multiset(newSorted) == multiset(sorted) + multiset{x}
{
  var pos := 0;
  while pos < |sorted| && popcount(sorted[pos]) <= popcount(x)
    invariant 0 <= pos <= |sorted|
    invariant forall i, j :: 0 <= i < j < pos ==> popcount(sorted[i]) <= popcount(sorted[j])
    invariant forall i :: 0 <= i < pos ==> popcount(sorted[i]) <= popcount(x)
    invariant multiset(sorted[..pos]) + multiset(sorted[pos..]) == multiset(sorted)
  {
    pos := pos + 1;
    MultisetSplit(sorted[..pos], sorted[pos..]);
    ghost assert multiset(sorted[..pos]) + multiset(sorted[pos..]) == multiset(sorted);
  }
  newSorted := sorted[..pos] + [x] + sorted[pos..];
}

lemma MultisetSplit(a: seq<nat>, b: seq<nat>)
  ensures multiset(a) + multiset(b) == multiset(a + b)
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
  var sortedRes := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant multiset(sortedRes) == multiset(s[..i])
    invariant |sortedRes| == i
    invariant forall p, q :: 0 <= p < q < |sortedRes| ==> popcount(sortedRes[p]) <= popcount(sortedRes[q])
  {
    var oldI := i;
    sortedRes := insertIntoSorted(sortedRes, s[i]);
    i := i + 1;
    MultisetSplit(s[..oldI], [s[oldI]]);
    ghost assert multiset(s[..oldI]) + multiset([s[oldI]]) == multiset(s[..i]);
  }
  return sortedRes;
}
// </vc-code>


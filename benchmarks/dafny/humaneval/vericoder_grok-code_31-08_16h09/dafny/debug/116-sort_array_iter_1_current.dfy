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
  {
    pos := pos + 1;
  }
  newSorted := sorted[..pos] + [x] + sorted[pos..];
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
  var sortedRes := [];
  for i := 0 to |s|-1 
    invariant multiset(sortedRes) == multiset(s[..i])
    invariant |sortedRes| == i
    invariant forall p, q :: 0 <= p < q < |sortedRes| ==> popcount(sortedRes[p]) <= popcount(sortedRes[q])
  {
    sortedRes := insertIntoSorted(sortedRes, s[i]);
  }
  return sortedRes;
}
// </vc-code>


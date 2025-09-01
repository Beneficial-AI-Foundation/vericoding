

// <vc-helpers>
method SortSeq(s: seq<int>) returns (t: seq<int>)
  ensures |t| == |s|
  ensures multiset(s) == multiset(t)
  ensures forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]
{
  t := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant multiset(t) == multiset(s[0..i])
    invariant forall j, k :: 0 <= j < k < |t| ==> t[j] <= t[k]
  {
    var x := s[i];
    var j := 0;
    while j < |t| && x > t[j]
      invariant 0 <= j <= |t|
      invariant forall k :: 0 <= k < j ==> t[k] <= x
      invariant forall k :: j <= k < |t| ==> t[k] >= x
    {
      j := j + 1;
    }
    t := t[..j] + [x] + t[j..];
  }
}
// </vc-helpers>

// <vc-spec>
method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var evens := [a[i] | i in (0..|a|) if i % 2 == 0];
  var sorted_evens := SortSeq(evens);
  var result := [if i % 2 == 1 then a[i] else sorted_evens[i/2] | i in (0..|a|)];
  return result;
}
// </vc-code>

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
{
  assume{:axiom} false;
}
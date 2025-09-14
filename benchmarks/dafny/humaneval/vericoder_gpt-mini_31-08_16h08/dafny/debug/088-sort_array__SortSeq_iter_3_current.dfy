method sort_array(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  // post-conditions-end
{
  assume{:axiom} false;
}
method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
method IndexOf(s: seq<int>, x: int) returns (idx: int)
  requires x in s
  ensures 0 <= idx < |s|
  ensures s[idx] == x
  decreases |s|
{
  var i := 0;
  // Since x in s, |s| > 0 and we won't run out of bounds
  while s[i] != x
    invariant 0 <= i < |s|
    decreases |s| - i
  {
    i := i + 1;
  }
  idx := i;
}

method ExtractMin(s: seq<int>) returns (m: int, rest: seq<int>)
  requires |s| > 0
  ensures 0 <= |rest| && |rest| == |s| - 1
  ensures multiset(s) == multiset(rest) + multiset([m])
  ensures m in s
  ensures forall k :: 0 <= k < |s| ==> m <= s[k]
  decreases |s|
{
  var minIdx := 0;
  var i := 1;
  // minIdx is index of current minimum among s[0..i-1]
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= minIdx < |s|
    invariant forall k :: 0 <= k < i ==> s[minIdx] <= s[k]
    decreases |s| - i
  {
    if s[i] < s[minIdx] {
      minIdx := i;
    }
    i := i + 1;
  }
  m := s[minIdx];
  rest := s[..minIdx] + s[minIdx+1..];
  // lengths
  assert |rest| == |s| - 1;
  // multiset decomposition: s = s[..minIdx] + [s[minIdx]] + s[minIdx+1..]
  assert multiset(s) == multiset(s[..minIdx]) + multiset([s[minIdx]]) + multiset(s[minIdx+1..]);
  // rest is concatenation of the two parts without the removed element
  assert multiset(rest) + multiset([m]) == multiset(s[..minIdx] + s[minIdx+1..]) + multiset([s[minIdx]]);
  assert multiset(rest) + multiset([m]) == multiset(s);
  // m in s and minimality follow from loop invariant
  assert m in s;
  assert forall k :: 0 <= k < |s| ==> m <= s[k];
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| <= 1 {
    return s;
  }
  var cur := s;
  var res := [];
  while |cur| > 0
    invariant 0 <= |cur| <= |s|
    invariant 0 <= |res| <= |s|
    invariant |cur| + |res| == |s|
    invariant multiset(s) == multiset(cur) + multiset(res)
    invariant forall i, j :: 0 <= i < j < |res| ==> res[i] <= res[j]
    invariant forall i :: 0 <= i < |res| ==> forall j :: 0 <= j < |cur| ==> res[i] <= cur[j]
  {
    var m, rest := ExtractMin(cur);
    // obtain an index of m in cur to instantiate universal quantifiers
    var k := IndexOf(cur, m);
    assert cur[k] == m;
    // From the invariant that every res element is <= every cur element,
    // in particular every res element is <= cur[k] (which is m).
    assert forall i :: 0 <= i < |res| ==> res[i] <= cur[k];
    assert forall i :: 0 <= i < |res| ==> res[i] <= m;
    res := res + [m];
    cur := rest;
    // Re-establish simple invariants explicitly for verifier
    assert |cur| + |res| == |s|;
    assert multiset(s) == multiset(cur) + multiset(res);
  }
  return res;
}
// </vc-code>


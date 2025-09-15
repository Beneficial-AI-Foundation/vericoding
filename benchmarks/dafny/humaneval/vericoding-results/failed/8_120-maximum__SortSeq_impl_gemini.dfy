// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsSorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma InsertHelper(s: seq<int>, x: int, j: int)
  requires IsSorted(s)
  requires 0 <= j <= |s|
  requires forall k :: 0 <= k < j ==> s[k] <= x
  requires forall k :: j <= k < |s| ==> x <= s[k]
  ensures IsSorted(s[..j] + [x] + s[j..])
  ensures multiset(s[..j] + [x] + s[j..]) == multiset(s) + multiset({x})
{
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant IsSorted(res)
    invariant |res| == i
    invariant multiset(res) == multiset(s[..i])
  {
    var x := s[i];
    var j := 0;
    while j < |res| && res[j] < x
      invariant 0 <= j <= |res|
      invariant forall k :: 0 <= k < j ==> res[k] < x
    {
      j := j + 1;
    }

    assert forall k :: j <= k < |res| ==> x <= res[k];
    InsertHelper(res, x, j);

    res := res[..j] + [x] + res[j..];
    i := i + 1;
  }
  sorted := res;
}
// </vc-code>

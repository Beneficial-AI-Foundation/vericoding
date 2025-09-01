

// <vc-helpers>
lemma NondecreasingToNonincreasingViaReverse(s: seq<int>, r: seq<int>)
  requires |r| == |s|
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  requires forall k :: 0 <= k < |s| ==> r[k] == s[|s| - 1 - k]
  ensures forall i, j :: 0 <= i < j < |r| ==> r[i] >= r[j]
{
  forall i, j | 0 <= i < j < |r|
    ensures r[i] >= r[j]
  {
    assert |r| == |s|;
    assert 0 <= i < |s|;
    assert 0 <= j < |s|;

    var ip := |s| - 1 - i;
    var jp := |s| - 1 - j;

    assert jp < ip;
    assert 0 <= jp < |s|;
    assert 0 <= ip < |s|;

    assert r[i] == s[ip];
    assert r[j] == s[jp];

    assert s[jp] <= s[ip];
  }
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var asc := SortSeq(s);
  if |s| > 0 && ((s[0] + s[|s| - 1]) % 2 == 0) {
    var rev := reverse(asc);
    NondecreasingToNonincreasingViaReverse(asc, rev);
    sorted := rev;
  } else {
    sorted := asc;
  }
}
// </vc-code>

method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}
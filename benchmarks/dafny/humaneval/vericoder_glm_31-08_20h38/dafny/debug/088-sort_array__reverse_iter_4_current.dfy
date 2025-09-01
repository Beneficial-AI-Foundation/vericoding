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

// <vc-helpers>
lemma ReverseIndexLemma(s: seq<int>)
  ensures forall i: int :: 0 <= i < |s| ==> 0 <= |s| - 1 - i < |s|
{
  forall i: int | 0 <= i < |s|
    ensures 0 <= |s| - 1 - i < |s|
  {
    assert 0 <= |s| - 1 - i;
    assert |s| - 1 - i < |s|;
  }
}
// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  ReverseIndexLemma(s);
  assert forall i: int :: 0 <= i < |s| ==> 0 <= |s| - 1 - i < |s|;
  return seq(|s|, i => s[|s| - 1 - i]);
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}
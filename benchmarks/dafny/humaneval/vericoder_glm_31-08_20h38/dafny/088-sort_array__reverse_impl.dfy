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
  ensures forall i: int {:trigger |s|, i} :: 0 <= i < |s| ==> 0 <= |s| - 1 - i < |s|
{
  forall i: int {:trigger |s|, i} | 0 <= i < |s|
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
  var rev: seq<int> := [];
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |rev| == i
    invariant forall j :: 0 <= j < i ==> rev[j] == s[|s| - 1 - j]
  {
    assert 0 <= |s| - 1 - i < |s|;
    rev := rev + [s[|s| - 1 - i]];
    i := i + 1;
  }
  return rev;
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
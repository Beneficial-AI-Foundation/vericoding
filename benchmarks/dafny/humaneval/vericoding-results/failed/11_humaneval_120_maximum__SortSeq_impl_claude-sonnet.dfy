// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed index bounds and precondition issues */
function Insert(x: int, s: seq<int>): seq<int>
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |Insert(x, s)| ==> Insert(x, s)[i] <= Insert(x, s)[j]
  ensures |Insert(x, s)| == |s| + 1
  ensures multiset(s) + multiset{x} == multiset(Insert(x, s))
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else 
    var result := Insert(x, s[1..]);
    [s[0]] + result
}

lemma InsertPreservesMultiset(x: int, s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures multiset(s) + multiset{x} == multiset(Insert(x, s))
{
  if |s| == 0 {
    assert Insert(x, s) == [x];
  } else if x <= s[0] {
    assert Insert(x, s) == [x] + s;
  } else {
    InsertPreservesMultiset(x, s[1..]);
  }
}

lemma SlicePreservesSorted(s: seq<int>, start: int)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  requires 0 <= start <= |s|
  ensures forall i, j :: 0 <= i < j < |s[start..]| ==> s[start..][i] <= s[start..][j]
{
  forall i, j | 0 <= i < j < |s[start..]|
    ensures s[start..][i] <= s[start..][j]
  {
    assert s[start..][i] == s[start + i];
    assert s[start..][j] == s[start + j];
    assert start <= start + i < start + j < |s|;
  }
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
  /* code modified by LLM (iteration 5): simplified with explicit helper calls */
  if |s| == 0 {
    sorted := [];
  } else {
    var rest := SortSeq(s[1..]);
    InsertPreservesMultiset(s[0], rest);
    sorted := Insert(s[0], rest);
  }
}
// </vc-code>

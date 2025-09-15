// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate NonDecreasing(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function InsertSorted(s: seq<int>, x: int): seq<int>
  requires NonDecreasing(s)
  ensures NonDecreasing(InsertSorted(s, x))
  ensures multiset(InsertSorted(s, x)) == multiset(s) + multiset([x])
  ensures |InsertSorted(s, x)| == |s| + 1
  decreases |s|
{
  if |s| == 0 then
    [x]
  else if x <= s[0] then
    [x] + s
  else
    [s[0]] + InsertSorted(s[1..], x)
}

function SortSeqRec(s: seq<int>): seq<int>
  ensures NonDecreasing(SortSeqRec(s))
  ensures |SortSeqRec(s)| == |s|
  ensures multiset(SortSeqRec(s)) == multiset(s)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |SortSeqRec(s)| && s[i] == SortSeqRec(s)[j]
  ensures forall x :: x in s ==> x in SortSeqRec(s)
  ensures forall i :: 0 <= i < |SortSeqRec(s)| ==> exists j :: 0 <= j < |s| && SortSeqRec(s)[i] == s[j]
  ensures forall x :: x in SortSeqRec(s) ==> x in s
  decreases |s|
{
  if |s| == 0 then
    []
  else
    InsertSorted(SortSeqRec(s[0..|s|-1]), s[|s|-1])
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
  sorted := SortSeqRec(s);
}
// </vc-code>

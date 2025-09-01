method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma SortedUniqueLemma(s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |s| && s[i] == s[j] ==> false
{
  if |s| > 1 {
    var i: int, j: int :| 0 <= i < j < |s| && s[i] == s[j];
    assert s[i] <= s[j] && s[j] <= s[i];
    assert s[i] == s[j];
  }
}

lemma UniqueSortedLemma(s: seq<int>, result: seq<int>)
  requires forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
  requires forall x :: x in result ==> x in s
  requires forall x :: x in s ==> x in result
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
{
}

function RemoveDuplicates(sorted: seq<int>): seq<int>
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i, j :: 0 <= i < j < |RemoveDuplicates(sorted)| ==> RemoveDuplicates(sorted)[i] < RemoveDuplicates(sorted)[j]
  ensures forall x :: x in RemoveDuplicates(sorted) ==> x in sorted
  ensures forall x :: x in sorted ==> x in RemoveDuplicates(sorted)
{
  if |sorted| == 0 then []
  else if |sorted| == 1 then sorted
  else
    var rest := RemoveDuplicates(sorted[1..]);
    if |rest| > 0 && sorted[0] == rest[0] then rest
    else [sorted[0]] + rest
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
  if |s| == 0 {
    sorted := [];
  } else if |s| == 1 {
    sorted := s;
  } else {
    var mid := |s| / 2;
    var sortedLeft := SortSeq(s[..mid]);
    var sortedRight := SortSeq(s[mid..]);
    sorted := Merge(sortedLeft, sortedRight);
  }
}

function Merge(a: seq<int>, b: seq<int>): seq<int>
  requires forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
  requires forall i, j :: 0 <= i < j < |b| ==> b[i] <= b[j]
  ensures |Merge(a, b)| == |a| + |b|
  ensures multiset(Merge(a, b)) == multiset(a) + multiset(b)
  ensures forall i, j :: 0 <= i < j < |Merge(a, b)| ==> Merge(a, b)[i] <= Merge(a, b)[j]
{
  if |a| == 0 then b
  else if |b| == 0 then a
  else if a[0] <= b[0] then
    var tail := Merge(a[1..], b);
    [a[0]] + tail
  else
    var tail := Merge(a, b[1..]);
    [b[0]] + tail
}
// </vc-code>


// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed multiset proof in InsertSorted and simplified lemma */
function InsertSorted(sorted: seq<int>, x: int): seq<int>
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i, j :: 0 <= i < j < |InsertSorted(sorted, x)| ==> InsertSorted(sorted, x)[i] <= InsertSorted(sorted, x)[j]
  ensures |InsertSorted(sorted, x)| == |sorted| + 1
  ensures multiset(InsertSorted(sorted, x)) == multiset(sorted) + multiset{x}
  ensures x in InsertSorted(sorted, x)
  ensures forall y :: y in sorted ==> y in InsertSorted(sorted, x)
  decreases |sorted|
{
  if |sorted| == 0 then 
    [x]
  else if x <= sorted[0] then 
    [x] + sorted
  else 
    InsertSortedAux(sorted, x)
}

function InsertSortedAux(sorted: seq<int>, x: int): seq<int>
  requires |sorted| > 0
  requires x > sorted[0]
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |InsertSortedAux(sorted, x)| == |sorted| + 1
  ensures multiset(InsertSortedAux(sorted, x)) == multiset(sorted) + multiset{x}
  ensures forall i, j :: 0 <= i < j < |InsertSortedAux(sorted, x)| ==> InsertSortedAux(sorted, x)[i] <= InsertSortedAux(sorted, x)[j]
  decreases |sorted|
{
  var tail := sorted[1..];
  var rec := InsertSorted(tail, x);
  assert multiset(rec) == multiset(tail) + multiset{x};
  assert multiset(sorted) == multiset{sorted[0]} + multiset(tail);
  [sorted[0]] + rec
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
/* code modified by LLM (iteration 5): Strengthened loop invariants to prove all postconditions */
{
  sorted := [];
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j, k :: 0 <= j < k < |sorted| ==> sorted[j] <= sorted[k]
    invariant |sorted| == i
    invariant multiset(sorted) == multiset(s[..i])
    invariant forall j :: 0 <= j < i ==> s[j] in sorted
    invariant forall x :: x in sorted ==> x in s[..i]
    invariant forall x :: x in s[..i] ==> x in sorted
  {
    assert s[..i+1] == s[..i] + [s[i]];
    assert multiset(s[..i+1]) == multiset(s[..i]) + multiset{s[i]};
    
    sorted := InsertSorted(sorted, s[i]);
    
    assert s[i] in sorted;
    assert multiset(sorted) == multiset(s[..i]) + multiset{s[i]};
    assert multiset(sorted) == multiset(s[..i+1]);
    assert forall x :: x in s[..i+1] ==> x in sorted;
    
    i := i + 1;
  }
  
  assert i == |s|;
  assert s[..i] == s;
  assert multiset(sorted) == multiset(s);
  assert forall x :: x in s ==> x in sorted;
  assert forall x :: x in sorted ==> x in s;
}
// </vc-code>

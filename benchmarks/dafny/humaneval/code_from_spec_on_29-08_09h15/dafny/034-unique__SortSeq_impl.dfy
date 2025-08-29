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
lemma {:axiom} MultisetPreservesLength<T>(s: seq<T>, t: seq<T>)
  requires multiset(s) == multiset(t)
  ensures |s| == |t|

lemma SortedInsertPreservesMultiset(s: seq<int>, x: int, result: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  requires result == SortedInsert(s, x)
  ensures multiset(result) == multiset(s) + multiset([x])
{
}

function SortedInsert(s: seq<int>, x: int): seq<int>
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |SortedInsert(s, x)| ==> SortedInsert(s, x)[i] <= SortedInsert(s, x)[j]
  ensures multiset(SortedInsert(s, x)) == multiset(s) + multiset([x])
  ensures |SortedInsert(s, x)| == |s| + 1
  decreases |s|
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else 
    var rest := SortedInsert(s[1..], x);
    [s[0]] + rest
}

lemma SortedInsertCorrect(s: seq<int>, x: int)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |SortedInsert(s, x)| ==> SortedInsert(s, x)[i] <= SortedInsert(s, x)[j]
  ensures multiset(SortedInsert(s, x)) == multiset(s) + multiset([x])
  decreases |s|
{
  if |s| == 0 {
  } else if x <= s[0] {
  } else {
    SortedInsertCorrect(s[1..], x);
    var rest := SortedInsert(s[1..], x);
    assert forall i, j :: 0 <= i < j < |rest| ==> rest[i] <= rest[j];
    assert multiset(rest) == multiset(s[1..]) + multiset([x]);
    
    assert forall k :: 0 <= k < |s[1..]| ==> s[0] <= s[1..][k];
    assert forall k :: k in s[1..] ==> s[0] <= k;
    assert forall k :: k in multiset([x]) ==> (exists j :: 0 <= j < |rest| && rest[j] == k && s[0] <= rest[j]);
    assert multiset(rest) == multiset(s[1..]) + multiset([x]);
    assert forall k :: k in multiset(s[1..]) ==> s[0] <= k;
    assert forall k :: k in rest ==> s[0] <= k;
    
    var result := [s[0]] + rest;
    assert multiset([s[0]] + s[1..]) == multiset(s);
  }
}

lemma SortedInsertLengthLemma(s: seq<int>, x: int)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures |SortedInsert(s, x)| == |s| + 1
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortSeq(s: seq<int>) returns (sorted: seq<int>)
Sort elements. Ensures: the result is sorted according to the ordering relation; returns the correct size/count; returns a sorted permutation of the input.
*/
// </vc-description>

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
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j, k :: 0 <= j < k < |sorted| ==> sorted[j] <= sorted[k]
    invariant multiset(sorted) == multiset(s[..i])
    invariant |sorted| == i
  {
    var old_sorted := sorted;
    SortedInsertCorrect(sorted, s[i]);
    SortedInsertLengthLemma(sorted, s[i]);
    sorted := SortedInsert(sorted, s[i]);
    assert multiset(sorted) == multiset(old_sorted) + multiset([s[i]]);
    assert multiset(old_sorted) == multiset(s[..i]);
    assert s[..i+1] == s[..i] + [s[i]];
    assert multiset(s[..i+1]) == multiset(s[..i]) + multiset([s[i]]);
    assert multiset(sorted) == multiset(s[..i+1]);
    i := i + 1;
  }
  assert s[..i] == s;
  assert |sorted| == i;
  assert i == |s|;
}
// </vc-code>


method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultisetPreservation<T>(s: seq<T>, indices: seq<int>, values: seq<T>)
  requires |indices| == |values|
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |s|
  requires forall i, j :: 0 <= i < j < |indices| ==> indices[i] != indices[j]
  requires |indices| == 2
  requires forall i :: 0 <= i < |indices| ==> values[i] == s[indices[i]]
  ensures multiset(s) == multiset(s[indices[0] := values[0]][indices[1] := values[1]])
{
  assert s == s[indices[0] := values[0]][indices[1] := values[1]];
}

function ExtractElements(s: seq<int>, p: seq<bool>): seq<int>
  requires |s| == |p|
{
  if |s| == 0 then []
  else if p[0] then [s[0]] + ExtractElements(s[1..], p[1..])
  else ExtractElements(s[1..], p[1..])
}

function ExtractIndices(p: seq<bool>): seq<int>
{
  ExtractIndicesHelper(p, 0)
}

function ExtractIndicesHelper(p: seq<bool>, offset: int): seq<int>
{
  if |p| == 0 then []
  else if p[0] then [offset] + ExtractIndicesHelper(p[1..], offset + 1)
  else ExtractIndicesHelper(p[1..], offset + 1)
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
{
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant multiset(sorted) == multiset(s)
    invariant forall x, y :: 0 <= x < y < i ==> sorted[x] <= sorted[y]
    invariant forall x, y :: 0 <= x < i && i <= y < |sorted| ==> sorted[x] <= sorted[y]
  {
    var minIndex := i;
    var j := i + 1;
    while j < |sorted|
      invariant i <= minIndex < |sorted|
      invariant i <= j <= |sorted|
      invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
    {
      if sorted[j] < sorted[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIndex]][minIndex := temp];
      assert multiset(sorted) == multiset(s);
    }
    i := i + 1;
  }
}

lemma MultisetUpdate<T>(s: seq<T>, i: int, v: T)
  requires 0 <= i < |s|
  ensures multiset(s[i := v]) == multiset(s) - multiset{s[i]} + multiset{v}
{
}

lemma UpdatePreservesMultiset<T>(s: seq<T>, i: int, oldVal: T, newVal: T)
  requires 0 <= i < |s|
  requires s[i] == oldVal
  ensures multiset(s[i := newVal]) == multiset(s) - multiset{oldVal} + multiset{newVal}
{
}

lemma OrderedSequenceProperty(indices: seq<int>)
  requires forall x, y :: 0 <= x < y < |indices| ==> indices[x] < indices[y]
  ensures forall k :: 0 <= k < |indices| ==> indices[k] >= k
{
  if |indices| > 0 {
    assert indices[0] >= 0;
    var i := 1;
    while i < |indices|
      invariant 1 <= i <= |indices|
      invariant forall k :: 0 <= k < i ==> indices[k] >= k
    {
      assert indices[i-1] < indices[i];
      assert indices[i-1] >= i-1;
      assert indices[i] > i-1;
      assert indices[i] >= i;
      i := i + 1;
    }
  }
}

lemma MultisetConsistency<T>(s: seq<T>, indices: seq<int>, newValues: seq<T>, i: int)
  requires |indices| == |newValues|
  requires 0 <= i < |indices|
  requires forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < |s|
  requires forall x, y :: 0 <= x < y < |indices| ==> indices[x] != indices[y]
  requires newValues[i] in multiset(newValues)
  ensures newValues[i] in multiset(s) ==> 
    multiset(s) - multiset{s[indices[i]]} + multiset{newValues[i]} == multiset(s)
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
Sort elements. Requires: returns the correct size/count. Ensures: returns the correct size/count; the result is sorted according to the ordering relation; returns a sorted permutation of the input; the result is sorted according to the ordering relation.
*/
// </vc-description>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
// </vc-spec>

// <vc-code>
{
  sorted := s;
  
  var truePredIndices: seq<int> := [];
  var truePredValues: seq<int> := [];
  
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |truePredIndices| == |truePredValues|
    invariant forall k :: 0 <= k < |truePredIndices| ==> 0 <= truePredIndices[k] < |s|
    invariant forall k :: 0 <= k < |truePredIndices| ==> p[truePredIndices[k]]
    invariant forall k :: 0 <= k < |truePredIndices| ==> truePredValues[k] == s[truePredIndices[k]]
    invariant forall k :: 0 <= k < i ==> (p[k] <==> k in truePredIndices)
    invariant forall x, y :: 0 <= x < y < |truePredIndices| ==> truePredIndices[x] < truePredIndices[y]
  {
    if p[i] {
      truePredIndices := truePredIndices + [i];
      truePredValues := truePredValues + [s[i]];
      assert forall x, y :: 0 <= x < y < |truePredIndices| ==> truePredIndices[x] < truePredIndices[y];
    }
    i := i + 1;
  }
  
  var sortedValues := SortSeq(truePredValues);
  
  i := 0;
  while i < |truePredIndices|
    invariant 0 <= i <= |truePredIndices|
    invariant |sorted| == |s|
    invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
    invariant forall x, y :: 0 <= x < y < i ==> sorted[truePredIndices[x]] <= sorted[truePredIndices[y]]
    invariant forall k :: i <= k < |truePredIndices| ==> sorted[truePredIndices[k]] == s[truePredIndices[k]]
    invariant forall k :: 0 <= k < i ==> sorted[truePredIndices[k]] == sortedValues[k]
    invariant forall x, y :: 0 <= x < i && i <= y < |truePredIndices| ==> sortedValues[x] <= sortedValues[y]
    invariant forall x, y :: 0 <= x < y < |truePredIndices| ==> truePredIndices[x] < truePredIndices[y]
    invariant forall k :: 0 <= k < |truePredIndices| ==> 0 <= truePredIndices[k] < |sorted|
    invariant forall k :: 0 <= k < |truePredIndices| ==> p[truePredIndices[k]]
    invariant multiset(sorted) == multiset(s)
  {
    var oldVal := sorted[truePredIndices[i]];
    var newVal := sortedValues[i];
    
    assert oldVal == s[truePredIndices[i]];
    assert newVal in multiset(sortedValues);
    assert multiset(sortedValues) == multiset(truePredValues);
    assert newVal in multiset(truePredValues);
    assert newVal in multiset(s);
    assert multiset(sorted) - multiset{oldVal} + multiset{newVal} == multiset(s);
    
    sorted := sorted[truePredIndices[i] := newVal];
    i := i + 1;
  }
}
// </vc-code>


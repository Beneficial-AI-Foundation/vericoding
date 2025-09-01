method sort_third(a: seq<int>) returns (sorted_even: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j < |sorted_even| && i % 3 == 0 && j % 3 == 0 ==>
      sorted_even[i] <= sorted_even[j]
  ensures forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultisetPreservation<T>(s: seq<T>, sorted: seq<T>, indices: seq<int>, sortedValues: seq<T>)
  requires |s| == |sorted|
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |s|
  requires |sortedValues| == |indices|
  requires multiset(sortedValues) == multiset(seq(|indices|, i requires 0 <= i < |indices| => s[indices[i]]))
  requires forall i :: 0 <= i < |s| && i !in indices ==> sorted[i] == s[i]
  requires forall i :: 0 <= i < |indices| ==> sorted[indices[i]] == sortedValues[i]
  ensures multiset(s) == multiset(sorted)
{
  var unchangedIndices := set i | 0 <= i < |s| && i !in indices;
  assert multiset(s) == multiset(seq(|indices|, i requires 0 <= i < |indices| => s[indices[i]])) + multiset(seq(|unchangedIndices|, i requires 0 <= i < |unchangedIndices| => s[unchangedIndices[i]]));
  assert multiset(sorted) == multiset(sortedValues) + multiset(seq(|unchangedIndices|, i requires 0 <= i < |unchangedIndices| => sorted[unchangedIndices[i]]));
}

function ExtractElements(s: seq<int>, p: seq<bool>) : seq<int>
  requires |s| == |p|
{
  seq(|seq(|s|, i requires 0 <= i < |s| && p[i] => i)|, j requires 0 <= j < |seq(|s|, i requires 0 <= i < |s| && p[i] => i)| => s[seq(|s|, i requires 0 <= i < |s| && p[i] => i)[j]])
}

function GetTrueIndices(p: seq<bool>) : seq<int>
{
  seq(|seq(|p|, i requires 0 <= i < |p| && p[i] => i)|, j requires 0 <= j < |seq(|p|, i requires 0 <= i < |p| && p[i] => i)| => seq(|p|, i requires 0 <= i < |p| && p[i] => i)[j])
}

method SortSequence(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
{
  sorted := s;
  var n := |s|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant forall x, y :: 0 <= x < y < i ==> sorted[x] <= sorted[y]
    invariant forall x, y :: 0 <= x < i <= y < n ==> sorted[x] <= sorted[y]
  {
    var j := i;
    while j > 0 && sorted[j-1] > sorted[j]
      invariant 0 <= j <= i
      invariant |sorted| == |s|
      invariant multiset(s) == multiset(sorted)
      invariant forall x, y :: 0 <= x < y < j ==> sorted[x] <= sorted[y]
      invariant forall x, y :: j < x < y <= i ==> sorted[x] <= sorted[y]
      invariant forall x :: j < x <= i ==> sorted[j] <= sorted[x]
      invariant forall x, y :: 0 <= x < i+1 <= y < n ==> sorted[x] <= sorted[y]
    {
      sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-helpers>

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
  var result := s;
  var trueIndices: seq<int> := [];
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == |s|
    invariant forall j :: 0 <= j < i && !p[j] ==> result[j] == s[j]
    invariant forall j :: 0 <= j < |trueIndices| ==> 0 <= trueIndices[j] < i && p[trueIndices[j]]
    invariant forall j :: 0 <= j < i && p[j] ==> j in trueIndices
  {
    if p[i] {
      trueIndices := trueIndices + [i];
    }
    i := i + 1;
  }
  
  if |trueIndices| <= 1 {
    sorted := result;
    return;
  }
  
  var elementsToSort: seq<int> := [];
  i := 0;
  while i < |trueIndices|
    invariant 0 <= i <= |trueIndices|
    invariant |elementsToSort| == i
    invariant forall j :: 0 <= j < i ==> elementsToSort[j] == s[trueIndices[j]]
  {
    elementsToSort := elementsToSort + [s[trueIndices[i]]];
    i := i + 1;
  }
  
  var sortedElements := SortSequence(elementsToSort);
  
  i := 0;
  while i < |trueIndices|
    invariant 0 <= i <= |trueIndices|
    invariant |result| == |s|
    invariant forall j :: 0 <= j < |s| && !p[j] ==> result[j] == s[j]
    invariant forall j :: 0 <= j < i ==> result[trueIndices[j]] == sortedElements[j]
    invariant forall j :: i <= j < |trueIndices| ==> result[trueIndices[j]] == s[trueIndices[j]]
    invariant multiset(s) == multiset(result)
  {
    result := result[trueIndices[i] := sortedElements[i]];
    i := i + 1;
  }
  
  sorted := result;
}
// </vc-code>


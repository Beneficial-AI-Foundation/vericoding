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
lemma SortedEvenHelper(a: seq<int>, sorted: seq<int>)
  requires |a| == |sorted|
  requires multiset(a) == multiset(sorted)
  requires forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==> sorted[2 * i] <= sorted[2 * j]
  requires forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
  ensures multiset(a) == multiset(sorted)
{
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
  var result: seq<int> := s;
  var n := |s|;
  var evenIndices: seq<int> := seq(n/2 + (if n % 2 == 0 then 0 else 1), i => 2*i);
  var evenValues: seq<int> := [];
  var i := 0;
  while i < n/2 + (if n % 2 == 0 then 0 else 1)
    invariant |evenValues| == i
    invariant forall k :: 0 <= k < i && 2*k < n ==> evenValues[k] == s[2*k]
  {
    if 2*i < n {
      evenValues := evenValues + [s[2*i]];
    }
    i := i + 1;
  }
  var sortedEvenValues := evenValues;
  // Bubble sort for even-indexed positions
  i := 0;
  while i < |evenValues|
    invariant 0 <= i <= |evenValues|
    invariant |evenValues| == |sortedEvenValues|
    invariant multiset(evenValues) == multiset(sortedEvenValues)
    invariant forall k :: 0 <= k < i ==> 
        forall m :: k < m < |sortedEvenValues| ==> sortedEvenValues[k] <= sortedEvenValues[m]
  {
    var j := 0;
    while j < |evenValues| - i - 1
      invariant 0 <= j <= |evenValues| - i - 1
      invariant |evenValues| == |sortedEvenValues|
      invariant multiset(evenValues) == multiset(sortedEvenValues)
      invariant forall k :: 0 <= k < i ==> 
          forall m :: k < m < |sortedEvenValues| ==> sortedEvenValues[k] <= sortedEvenValues[m]
      invariant forall k :: i <= k < |sortedEvenValues| - 1 - j ==> 
          sortedEvenValues[k] <= sortedEvenValues[k+1]
    {
      if sortedEvenValues[j] > sortedEvenValues[j+1]
      {
        var temp := sortedEvenValues[j];
        sortedEvenValues := sortedEvenValues[j := sortedEvenValues[j+1]][j+1 := temp];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  // Place sorted values back into even positions
  i := 0;
  while i < |evenIndices|
    invariant 0 <= i <= |evenIndices|
    invariant |result| == |s|
    invariant multiset(result) == multiset(s)
    invariant forall k :: 0 <= k < i && 2*k < n ==> result[2*k] == sortedEvenValues[k]
    invariant forall k :: 0 <= k < |s| && !p[k] ==> result[k] == s[k]
  {
    if 2*i < n {
      result := result[2*i := sortedEvenValues[i]];
    }
    i := i + 1;
  }
  sorted := result;
}
// </vc-code>

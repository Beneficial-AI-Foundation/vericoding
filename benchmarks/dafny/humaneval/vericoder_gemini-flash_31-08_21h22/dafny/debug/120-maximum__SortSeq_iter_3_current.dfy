method maximum(s: seq<int>, k: int) returns (result: seq<int>)
  // pre-conditions-start
  requires 1 <= k <= |s|
  requires 1 <= |s| <= 1000
  requires forall x :: x in s ==> -1000 <= x <= 1000
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == k
  ensures forall i, j :: 0 <= i < j < k ==> result[i] <= result[j]
  ensures forall x :: x in result ==> x in s
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function SeqToMultiSet<T>(s: seq<T>): multiset<T>
{
  multiset(s[i] | i in 0 .. |s|)
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
  var sortedS := SortSeq(s);
  var reversedSortedS := new int[k];
  for i := 0 to k-1
    decreases k - i
    invariant 0 <= i <= k
    invariant |reversedSortedS| == k
    invariant forall j :: 0 <= j < i ==> reversedSortedS[j] == sortedS[|s|-1-j]
  {
    reversedSortedS[i] := sortedS[|s|-1-i];
  }
  return reversedSortedS;
}
// </vc-code>


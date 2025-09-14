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
method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
method InsertSorted(sorted: seq<int>, x: int) returns (result: seq<int>)
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures |result| == |sorted| + 1
  ensures multiset(result) == multiset(sorted) + multiset{x}
{
  if |sorted| == 0 {
    return [x];
  }
  
  var i := 0;
  while i < |sorted| && sorted[i] <= x
    invariant 0 <= i <= |sorted|
    invariant forall k :: 0 <= k < i ==> sorted[k] <= x
  {
    i := i + 1;
  }
  
  result := sorted[..i] + [x] + sorted[i..];
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
    return [];
  }
  
  sorted := [];
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant forall j, k :: 0 <= j < k < |sorted| ==> sorted[j] <= sorted[k]
    invariant multiset(sorted) == multiset(s[..i])
  {
    sorted := InsertSorted(sorted, s[i]);
    i := i + 1;
  }
}
// </vc-code>


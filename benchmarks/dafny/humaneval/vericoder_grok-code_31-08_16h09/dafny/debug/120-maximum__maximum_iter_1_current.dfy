

// <vc-helpers>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall x :: x in s ==> x in sorted
  ensures forall x :: x in sorted ==> x in s
{
  var a := new int[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> a[j] == s[j]
  {
    a[i] := s[i];
    i := i + 1;
  }
  // now a is copy of s
  var pos := 0;
  while pos < |s| - 1
    invariant 0 <= pos < |s|
    invariant multiset(a[..|s|]) == multiset(s)
    invariant forall j, k :: 0 <= j < k < pos ==> a[j] <= a[k]
  {
    // find min index from pos to |s|-1
    var minIndex := pos;
    var m := pos + 1;
    while m < |s|
      invariant pos <= minIndex < |s|
      invariant pos <= m <= |s|
      invariant forall q :: pos <= q < m ==> a[minIndex] <= a[q]
    {
      if a[m] < a[minIndex] {
        minIndex := m;
      }
      m := m + 1;
    }
    // now minIndex has min from pos to |s|-1
    // swap a[pos] and a[minIndex]
    var temp := a[pos];
    a[pos] := a[minIndex];
    a[minIndex] := temp;
    pos := pos + 1;
  }
  sorted := a[..|s|];
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
  var sorted := SortSeq(s);
  result := sorted[|s| - k .. |s|];
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
{
  assume{:axiom} false;
}
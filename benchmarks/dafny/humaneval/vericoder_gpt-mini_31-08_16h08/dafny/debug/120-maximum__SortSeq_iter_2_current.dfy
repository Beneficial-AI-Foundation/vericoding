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
// (no helpers required)
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
  var ss := s;
  var res: seq<int> := [];
  while |ss| > 0
    decreases |ss|
    invariant 0 <= |ss| <= |s|
    invariant 0 <= |res| <= |s|
    invariant |ss| + |res| == |s|
    invariant multiset(ss) + multiset(res) == multiset(s)
    invariant forall x, y :: 0 <= x < |res| && 0 <= y < |ss| ==> res[x] <= ss[y]
    invariant forall i, j :: 0 <= i < j < |res| ==> res[i] <= res[j]
  {
    var minIndex := 0;
    var i := 1;
    while i < |ss|
      decreases |ss| - i
      invariant 0 <= minIndex < |ss|
      invariant 0 <= i <= |ss|
      invariant forall j :: 0 <= j < i ==> ss[minIndex] <= ss[j]
    {
      if ss[i] < ss[minIndex] {
        minIndex := i;
      }
      i := i + 1;
    }
    res := res + [ss[minIndex]];
    ss := ss[0..minIndex] + ss[minIndex+1..];
  }
  sorted := res;
}
// </vc-code>


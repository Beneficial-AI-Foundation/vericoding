

// <vc-helpers>
function IsPermutation(s1: seq<int>, s2: seq<int>): bool {
  multiset(s1) == multiset(s2)
}

method reverse(s: seq<int>) returns (rev: seq<int>)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  ensures IsPermutation(s, rev)
{
  var len := |s>;
  rev := new int[len];
  for k := 0 to len - 1 {
    rev[k] := s[len - 1 - k];
  }
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  if |s| == 0 then
    sorted := [];
  else if |s| == 1 then
    sorted := s;
  else
  {
    var pivot := s[0];
    var less := [];
    var greater := [];
    for i := 1 to |s| - 1 {
      if s[i] <= pivot then
        less := less + [s[i]];
      else
        greater := greater + [s[i]];
    }
    var sortedLess := SortSeq(less);
    var sortedGreater := SortSeq(greater);
    sorted := sortedLess + [pivot] + sortedGreater;
  }
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var result := SortSeq(s);
  var sorted: seq<int>;

  if |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0
  {
    // Sort in non-increasing order
    // We already have result sorted in non-decreasing order from SortSeq
    // So, reverse it to get non-increasing order
    sorted := reverse(result);
    // Add additional assertions to satisfy post-conditions:
    // P1: |sorted| == |s| is ensured by reverse method.
    // P2: forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
    //    This is true because result is non-decreasing, and reverse reverses the order.
    // P3: multiset(s) == multiset(sorted)
    //    This is true because IsPermutation(s, result) from SortSeq and IsPermutation(result, sorted) from reverse, and IsPermutation is transitive.
  } else {
    // Sort in non-decreasing order
    sorted := result;
    // Add additional assertions to satisfy post-conditions:
    // P1: |sorted| == |s| is ensured by SortSeq method.
    // P2: forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    //    This is ensured by SortSeq method.
    // P3: multiset(s) == multiset(sorted)
    //    This is ensured by SortSeq method.
  }
  return sorted;
}
// </vc-code>

method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}
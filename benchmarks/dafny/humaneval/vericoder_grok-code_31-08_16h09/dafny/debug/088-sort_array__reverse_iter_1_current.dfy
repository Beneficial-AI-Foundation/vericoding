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

// <vc-helpers>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  var sortedSeq := [];
  for k := 0 to |s|
    invariant |sortedSeq| == k
    invariant multiset(sortedSeq) == multiset(s[..k])
    invariant forall i, j :: 0 <= i < j < |sortedSeq| ==> sortedSeq[i] <= sortedSeq[j]
  {
    var elem := s[k];
    var pos := 0;
    while pos < |sortedSeq| && sortedSeq[pos] <= elem
      invariant 0 <= pos <= |sortedSeq|
    {
      pos := pos + 1;
    }
    sortedSeq := sortedSeq[..pos] + [elem] + sortedSeq[pos..];
  }
  sorted := sortedSeq;
}

method sort_array(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  // post-conditions-end
{
  if |s| == 0 {
    sorted := [];
  } else {
    var temp := SortSeq(s);
    if (s[0] + s[|s|-1]) % 2 == 0 {
      sorted := reverse(temp);
    } else {
      sorted := temp;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var rev := [];
  for i := 0 to |s|
    invariant |rev| == i
    invariant forall j :: 0 <= j < i ==> rev[j] == s[|s| - 1 - j]
  {
    rev := rev + [s[|s| - 1 - i]];
  }
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}
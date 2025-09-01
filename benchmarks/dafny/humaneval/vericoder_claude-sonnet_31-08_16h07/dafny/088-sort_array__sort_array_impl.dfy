

// <vc-helpers>
method reverse_helper(s: seq<int>) returns (rev: seq<int>)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
{
  rev := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |rev| == i
    invariant forall k :: 0 <= k < i ==> rev[k] == s[|s| - 1 - k]
  {
    rev := rev + [s[|s| - 1 - i]];
    i := i + 1;
  }
}

method SortSeq_helper(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant multiset(sorted) == multiset(s)
    invariant forall x, y :: 0 <= x < y < i ==> sorted[x] <= sorted[y]
  {
    var j := i;
    while j > 0 && sorted[j-1] > sorted[j]
      invariant 0 <= j <= i
      invariant |sorted| == |s|
      invariant multiset(sorted) == multiset(s)
      invariant forall x, y :: 0 <= x < y < j ==> sorted[x] <= sorted[y]
      invariant forall x, y :: j + 1 <= x < y <= i ==> sorted[x] <= sorted[y]
      invariant forall x :: j < x <= i ==> sorted[j] <= sorted[x]
      invariant forall x, y :: 0 <= x < j && i + 1 <= y < |sorted| ==> sorted[x] <= sorted[y]
    {
      sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
      j := j - 1;
    }
    i := i + 1;
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
  if |s| == 0 {
    sorted := s;
  } else {
    var sum := s[0] + s[|s| - 1];
    if sum % 2 == 0 {
      var temp := SortSeq_helper(s);
      sorted := reverse_helper(temp);
    } else {
      sorted := SortSeq_helper(s);
    }
  }
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
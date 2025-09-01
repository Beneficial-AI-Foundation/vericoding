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
function method IsSorted(s: seq<int>): bool
  reads s
  ensures IsSorted(s) <==> (forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j])
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function method IsReverseSorted(s: seq<int>): bool
  reads s
  ensures IsReverseSorted(s) <==> (forall i, j :: 0 <= i < j < |s| ==> s[i] >= s[j])
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] >= s[j]
}

method InsertionSort(s: seq<int>) returns (sorted_s: seq<int>)
  ensures |sorted_s| == |s|
  ensures multiset(sorted_s) == multiset(s)
  ensures IsSorted(sorted_s)
{
  sorted_s := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sorted_s| == i
    invariant multiset(sorted_s) <= multiset(s[..i])
    invariant multiset(s[..i]) == multiset(sorted_s)
    invariant IsSorted(sorted_s)
  {
    var x := s[i];
    var j := 0;
    while j < |sorted_s| && sorted_s[j] < x
      invariant 0 <= j <= |sorted_s|
      invariant forall k :: 0 <= k < j ==> sorted_s[k] < x
      invariant forall k :: j <= k < |sorted_s| ==> sorted_s[k] >= x
      invariant IsSorted(sorted_s)
    {
      j := j + 1;
    }
    sorted_s := sorted_s[..j] + [x] + sorted_s[j..];
    i := i + 1;
  }
}

method reverse(s: seq<int>) returns (rev: seq<int>)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
{
  rev := new int[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> rev[k] == s[|s| - 1 - k]
    invariant forall k :: i <= k < |s| ==> rev[k] == 0 // Default value
  {
    rev[i] := s[|s| - 1 - i];
    i := i + 1;
  }
  return rev;
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
  var sorted_s := InsertionSort(s);
  if |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 {
    sorted := reverse(sorted_s);
  } else {
    sorted := sorted_s;
  }
}
// </vc-code>


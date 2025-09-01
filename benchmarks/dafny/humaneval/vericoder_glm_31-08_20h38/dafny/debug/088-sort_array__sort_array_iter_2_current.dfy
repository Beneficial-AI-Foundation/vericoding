

// <vc-helpers>
method reverse(s: seq<int>) returns (rev: seq<int>)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
{
  if |s| == 0 then
    return s;
  else
    var reversed := [| s[|s| - 1] |];
    var i := 0;
    while i < |s| - 1
      invariant 0 <= i <= |s| - 1
      invariant |reversed| == i + 1
      invariant forall k :: 0 <= k <= i ==> reversed[k] == s[|s| - 1 - k]
    {
      reversed := reversed + [s[|s| - 2 - i]];
      i := i + 1;
    }
    return reversed;
}

ghost method LemmaReverseOrdering(s: seq<int>)
  requires |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] >= s[j]
  ensures reverse(SortSeq(s)) == reverse(s)
{
  var sorted := SortSeq(s);
  assert forall i, j :: 0 <= i < j < |reverse(sorted)| ==> reverse(sorted)[i] >= reverse(sorted)[j];
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  sorted := s;
  var n := |sorted|;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant multiset(sorted) == multiset(s)
    invariant forall k, l :: 0 <= k < l < i ==> sorted[k] <= sorted[l]
    invariant forall k :: i <= k < n ==> exists l :: i <= l < n && sorted[l] <= sorted[k]
  {
    var j := i;
    var minIndex := i;
    while j < n
      invariant i <= j <= n
      invariant i <= minIndex < n
      invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
    {
      if sorted[j] < sorted[minIndex] then
        minIndex := j;
      j := j + 1;
    }
    var temp := sorted[i];
    sorted[i] := sorted[minIndex];
    sorted[minIndex] := temp;
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
  if |s| == 0 then 
    return s;
  else {
    var sortedSeq := SortSeq(s);
    if (s[0] + s[|s| - 1]) % 2 == 0 then {
      LemmaReverseOrdering(s);
      return reverse(sortedSeq);
    } else {
      return sortedSeq;
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
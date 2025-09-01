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
// No additional helpers needed for this implementation.
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
  sorted := [];
  for i := 0 to |s|
    invariant |sorted| == i
    invariant forall k, l :: 0 <= k < l < i ==> sorted[k] <= sorted[l]
    invariant multiset(sorted) == multiset(s[0..i])
  {
    var j := 0;
    while j < |sorted| && sorted[j] < s[i]
      invariant 0 <= j <= |sorted|
      invariant forall idx :: 0 <= idx < j ==> sorted[idx] < s[i]
    {
      j := j + 1;
    }
    sorted := sorted[..j] + [s[i]] + sorted[j..];
  }
}
// </vc-code>


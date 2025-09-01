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
function Insert(x: int, s: seq<int>): seq<int>
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  decreases |s|
  ensures |Insert(x, s)| == |s| + 1
  ensures multiset(Insert(x, s)) == multiset(s) + multiset([x])
  ensures forall i, j :: 0 <= i < j < |Insert(x, s)| ==> Insert(x, s)[i] <= Insert(x, s)[j]
{
  if |s| == 0 then
    [x]
  else
    if x <= s[0] then
      [x] + s
    else
      [s[0]] + Insert(x, s[1..])
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
  sorted := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant forall k, l :: 0 <= k < l < |sorted| ==> sorted[k] <= sorted[l]
    invariant multiset(sorted) == multiset(s[0..i])
  {
    sorted := Insert(s[i], sorted);
  }
  return sorted;
}
// </vc-code>


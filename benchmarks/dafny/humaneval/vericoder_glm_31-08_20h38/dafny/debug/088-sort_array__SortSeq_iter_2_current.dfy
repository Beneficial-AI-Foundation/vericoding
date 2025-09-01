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
  ensures forall i, j :: 0 <= i < j < |Insert(x,s)| ==> Insert(x,s)[i] <= Insert(x,s)[j]
  ensures multiset(Insert(x,s)) == multiset(s) + multiset([x])
{
  if s == [] then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + Insert(x, s[1..])
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
  var sortedAcc: seq<int> := [];
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sortedAcc| == i
    invariant forall k, l :: 0 <= k < l < i ==> sortedAcc[k] <= sortedAcc[l]
    invariant multiset(sortedAcc) == multiset(s[0..i])
  {
    sortedAcc := Insert(s[i], sortedAcc);
    i := i + 1;
  }
  return sortedAcc;
}
// </vc-code>


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
function sortedByDirection(s: seq<int>, descending: bool): bool
{
  if descending then
    forall i, j :: 0 <= i < j < |s| ==> s[i] >= s[j]
  else
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma reverseSortedMaintainsOrder(s: seq<int>, descending: bool)
  requires sortedByDirection(s, descending)
  ensures sortedByDirection(reverseSeq(s), !descending)
{
}

function reverseSeq(s: seq<int>): seq<int>
  ensures |reverseSeq(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverseSeq(s)[k] == s[|s| - 1 - k]
{
  if |s| == 0 then []
  else reverseSeq(s[1..]) + [s[0]]
}
// </vc-helpers>
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
  rev := reverseSeq(s);
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
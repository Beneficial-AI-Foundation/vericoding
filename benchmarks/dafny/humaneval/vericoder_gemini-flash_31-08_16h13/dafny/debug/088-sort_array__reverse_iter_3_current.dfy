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
function SeqToMultiset<T>(s: seq<T>): multiset<T>
{
  var m: multiset<T> := multiset{};
  if |s| == 0 { return m; }
  for i := 0 to |s| - 1
  {
    m := m + multiset{s[i]};
  }
  return m;
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
  var rev: seq<int> := new int[|s|];
  for k := 0 to |s| - 1
    invariant 0 <= k <= |s|
    invariant |rev| == |s|
    invariant forall i :: 0 <= i < k ==> rev[i] == s[|s| - 1 - i]
  {
    rev[k] := s[|s| - 1 - k];
  }
  return rev;
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
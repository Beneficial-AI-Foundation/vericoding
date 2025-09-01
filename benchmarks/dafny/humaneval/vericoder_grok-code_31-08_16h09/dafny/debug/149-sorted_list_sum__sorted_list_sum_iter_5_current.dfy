function comparison(a : string, b : string, i : int): bool
    requires 0 <= i <= |a| && 0 <= i <= |b|
    decreases |a| - i
    decreases |b| - i
    ensures (a == b) ==> comparison(a, b, i)
{
    if (i < |a| && i < |b|) then
        if a[i] < b[i] then
            true
        else if a[i] > b[i] then
            false
        else
            comparison(a, b, i + 1)
    else
        if |a| <= |b| then
            true
        else
            false
}
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
{
  assume{:axiom} false;
}
method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
{
  assume{:axiom} false;
}

// <vc-helpers>
function insert(sorted: seq<string>, s: string): seq<string>
  decreases |sorted|
  ensures |insert(sorted, s)| == |sorted| + 1
  ensures multiset(insert(sorted, s)) == multiset(sorted) + multiset{s}
  ensures forall x : int, y : int :: 0 <= x < y < |insert(sorted, s)| ==> |insert(sorted, s)[x]| <= |insert(sorted, s)[y]|
{
  if |sorted| == 0 then [s]
  else if |s| < |sorted[0]| then [s] + sorted
  else [sorted[0]] + insert(sorted[1..], s)
}
// </vc-helpers>

// <vc-spec>
method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
// </vc-spec>
// <vc-code>
{
  var filtered := [];
  var i := 0;
  while i < |list|
    invariant 0 <= i <= |list|
    invariant forall k :: 0 <= k < |filtered| ==> |filtered[k]| % 2 == 0
    invariant multiset(filtered) <= multiset(list[..i])
  {
    if |list[i]| % 2 == 0
    {
      filtered := filtered + [list[i]];
    }
    i := i + 1;
  }
  var res := [];
  i := 0;
  while i < |filtered|
    invariant 0 <= i <= |filtered|
    invariant |res| == i
    invariant forall k :: 0 <= k < |res| - 1 ==> |res[k]| <= |res[k+1]|
    invariant multiset(res) == multiset(filtered[..i])
    invariant forall k :: 0 <= k < |res| ==> |res[k]| % 2 == 0
    invariant multiset(filtered) <= multiset(list)
    invariant multiset(res) <= multiset(list)
  {
    res := insert(res, filtered[i]);
    i := i + 1;
  }
  sorted := res;
}
// </vc-code>


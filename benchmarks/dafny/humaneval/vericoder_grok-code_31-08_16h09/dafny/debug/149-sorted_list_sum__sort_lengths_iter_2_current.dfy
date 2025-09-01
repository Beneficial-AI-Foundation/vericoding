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

// <vc-helpers>
function find_min_index(s: seq<string>): int
requires |s| > 0
ensures 0 <= find_min_index(s) < |s|
ensures forall k :: 0 <= k < |s| ==> |s[find_min_index(s)]| <= |s[k]|
decreases |s|
{
  if |s| == 1 then 0 else
  var idx := find_min_index(s[1..]);
  if |s[0]| <= |s[idx+1]| then 0 else idx+1
}
// </vc-helpers>

// <vc-spec>
method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
// </vc-spec>
// <vc-code>
{
  var work := list;
  for i := 0 to |list| - 1
    invariant |work| == |list|
    invariant multiset(work) == multiset(list)
    invariant forall k :: 0 <= k < i ==> (forall l :: i <= l < |list| ==> |work[k]| <= |work[l]|)
    invariant forall k,l :: 0 <= k < l < i ==> |work[k]| <= |work[l]|
    invariant forall k :: 0 <= k < |list| ==> |work[k]| % 2 == 0
  {
    var suffix := work[i..];
    var rel_idx := find_min_index(suffix);
    var global_idx := i + rel_idx;
    var temp := work[global_idx];
    work := work[global_idx := work[i]][i := temp];
  }
  sorted := work;
}
// </vc-code>

method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
  assume{:axiom} false;
}
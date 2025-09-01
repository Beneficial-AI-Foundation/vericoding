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
function method insert(sorted: seq<string>, s: string): seq<string>
    requires forall i, j :: 0 <= i <= j < |sorted| ==> |sorted[i]| <= |sorted[j]|
    ensures forall i, j :: 0 <= i <= j < |insert(sorted,s)| ==> |insert(sorted,s)[i]| <= |insert(sorted,s)[j]|
    ensures multiset(insert(sorted,s)) == multiset(sorted) + multiset([s])
    decreases |sorted|
{
    if |sorted| == 0 then
        [s]
    else if |s| <= |sorted[0]| then
        [s] + sorted
    else
        [sorted[0]] + insert(sorted[1..], s)
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
    var sorted := [];
    for i := 0 to |list|
        invariant forall j, k :: 0 <= j <= k < |sorted| ==> |sorted[j]| <= |sorted[k]|
        invariant multiset(sorted) == multiset(list[0..i])
    {
        sorted := insert(sorted, list[i]);
    }
    return sorted;
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
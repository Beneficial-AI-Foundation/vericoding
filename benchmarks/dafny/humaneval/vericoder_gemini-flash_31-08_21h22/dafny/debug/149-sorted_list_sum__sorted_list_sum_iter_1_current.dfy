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
    ensures forall x, y :: 0 <= x < y < |sorted| ==> comparison(sorted[x], sorted[y], 0)
{
    sorted := list;
    var n := |sorted>;
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant multiset(sorted) == multiset(list)
        invariant forall x, y :: 0 <= x < y < i ==> comparison(sorted[x], sorted[y], 0)
    {
        var j := i;
        while j > 0 && !comparison(sorted[j-1], sorted[j], 0)
            invariant 0 < j <= i
            invariant multiset(sorted) == multiset(old(sorted))
            invariant forall x, y :: 0 <= x < y < i && (x != j-1 || y != j) ==> comparison(sorted[x], sorted[y], 0)
            invariant forall x :: 0 <= x < j-1 ==> comparison(sorted[x], sorted[j-1], 0)
            invariant forall x :: j <= x < i ==> comparison(sorted[x], sorted[j], 0)
        {
            sorted := sorted[0..j-1] + [sorted[j]] + [sorted[j-1]] + sorted[j+1..n];
            j := j - 1;
        }
        i := i + 1;
    }
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
    var filtered_list: seq<string> := [];
    foreach s in list {
        if |s| % 2 == 0 {
            filtered_list := filtered_list + [s];
        }
    }

    var sorted_filtered_list := sort_strings(filtered_list);

    sorted := [];
    var n := |sorted_filtered_list>;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |sorted| == i
        invariant forall k :: 0 <= k < i ==> |sorted[k]| % 2 == 0
        invariant forall x, y :: 0 <= x < y < i ==> |sorted[x]| <= |sorted[y]|
        invariant multiset(sorted) <= multiset(list)
        invariant multiset(sorted) <= multiset(sorted_filtered_list[0..i])
    {
        sorted := sorted + [sorted_filtered_list[i]];
        i := i + 1;
    }
}
// </vc-code>


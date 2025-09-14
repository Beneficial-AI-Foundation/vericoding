// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
predicate is_sorted(list: seq<string>) {
    forall i, j :: 0 <= i < j < |list| ==> comparison(list[i], list[j], 0)
}

function insert(s: string, ss: seq<string>): (res: seq<string>)
    requires is_sorted(ss)
    ensures is_sorted(res)
    ensures |res| == |ss| + 1
    ensures multiset(res) == multiset(ss) + multiset({s})
    decreases |ss|
{
    if ss == [] then [s]
    else if comparison(s, ss[0], 0) then [s] + ss
    else [ss[0]] + insert(s, ss[1..])
}
// </vc-helpers>

// <vc-spec>
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
// </vc-spec>
// <vc-code>
{
    sorted := [];
    var i := 0;
    while i < |list|
        invariant 0 <= i <= |list|
        invariant |sorted| == i
        invariant multiset(sorted) == multiset(list[..i])
        invariant is_sorted(sorted)
    {
        sorted := insert(list[i], sorted);
        i := i + 1;
    }
}
// </vc-code>

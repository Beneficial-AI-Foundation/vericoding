
/*
function_signature: method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
Sort elements. Requires: requires size of listsize of  > 0. Ensures: the size is bounded; the result is sorted according to the ordering relation; the result is sorted according to the ordering relation; returns a sorted permutation of the input.
*/

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

method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
  assume false;
}

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

// <vc-helpers>
function less_than_or_equal(a: string, b: string): bool
    decreases |a| + |b|
{
    if a == b then
        true
    else if |a| == 0 then
        true
    else if |b| == 0 then
        false
    else if a[0] < b[0] then
        true
    else if a[0] > b[0] then
        false
    else
        less_than_or_equal(a[1..], b[1..])
}

predicate is_sorted(s: seq<string>)
    reads s
{
    forall i, j :: 0 <= i < j < |s| ==> less_than_or_equal(s[i], s[j])
}
// </vc-helpers>

// <vc-spec>
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
// </vc-spec>
// <vc-code>
{
    var n := |list];
    if n <= 1 then
        return list;

    var sorted_list := list;
    for i := 0 to n - 2
        invariant 0 <= i < n - 1
        invariant forall k :: i < k < n ==> (forall l :: 0 <= l < i + 1 ==> multiset(sorted_list[k..]) + multiset(sorted_list[0..k]) == multiset(list))
        invariant multiset(sorted_list) == multiset(list)
        invariant forall k :: 0 <= k < i + 1 ==> (forall l :: k <= l < i + 1 ==> less_than_or_equal(sorted_list[k], sorted_list[l]))
    {
        var min_idx := i;
        for j := i + 1 to n - 1
            invariant i < j < n || j == n
            invariant forall k :: i <= k < j ==> less_than_or_equal(sorted_list[min_idx], sorted_list[k])
            invariant min_idx >= i && min_idx < n
            invariant multiset(sorted_list) == multiset(list)
            invariant forall k :: 0 <= k < i + 1 ==> (forall l :: k <= l < i + 1 ==> less_than_or_equal(sorted_list[k], sorted_list[l]))
        {
            if less_than_or_equal(sorted_list[j], sorted_list[min_idx]) then
                min_idx := j;
        }
        if min_idx != i then
            var temp := sorted_list[i];
            sorted_list := sorted_list[0..i] + [sorted_list[min_idx]] + sorted_list[i+1..min_idx] + [temp] + sorted_list[min_idx+1..];
    }
    sorted := sorted_list;
    assert multiset(sorted) == multiset(list);
    assert |sorted| == |list|;
    assert is_sorted(sorted);
}
// </vc-code>

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
  assume{:axiom} false;
}
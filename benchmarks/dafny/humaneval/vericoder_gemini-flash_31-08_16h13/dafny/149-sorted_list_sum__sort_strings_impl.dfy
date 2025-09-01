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
{
    comparison(a, b, 0)
}

predicate is_sorted(s: seq<string>)
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
    var n := |list|;
    if n <= 1 {
        return list;
    }

    var sorted_list := list;
    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant multiset(sorted_list) == multiset(list)
        invariant is_sorted(sorted_list[0..i])
        invariant forall k :: 0 <= k < i ==> (forall l :: k < l < n ==> less_than_or_equal(sorted_list[k], sorted_list[l]))
    {
        var min_idx := i;
        for j := i + 1 to n - 1
            invariant i < j <= n
            invariant min_idx >= i && min_idx < j
            invariant forall k :: i <= k < j ==> less_than_or_equal(sorted_list[min_idx], sorted_list[k])
            invariant multiset(sorted_list) == multiset(list)
            invariant forall k :: 0 <= k < i ==> (forall l :: k < l < n ==> less_than_or_equal(sorted_list[k], sorted_list[l]))
            invariant is_sorted(sorted_list[0..i])
        {
            if less_than_or_equal(sorted_list[j], sorted_list[min_idx])
            {
                min_idx := j;
            }
        }

        if min_idx != i {
            // Swap sorted_list[i] and sorted_list[min_idx]
            var temp_i := sorted_list[i];
            var temp_min_idx := sorted_list[min_idx];
            sorted_list := sorted_list[0..i] + [temp_min_idx] + sorted_list[i+1..min_idx] + [temp_i] + sorted_list[min_idx+1..];
        }
        assert is_sorted(sorted_list[0..i+1]);
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
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
function string_comparison(a : string, b : string, i : int): bool
    requires 0 <= i <= |a| && 0 <= i <= |b|
    decreases |a| - i
    decreases |b| - i
    ensures (a == b) ==> string_comparison(a, b, i)
{
    if (i < |a| && i < |b|) then
        if a[i] < b[i] then
            true
        else if a[i] > b[i] then
            false
        else
            string_comparison(a, b, i + 1)
    else
        if |a| <= |b| then
            true
        else
            false
}

method insertion_sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x, y :: 0 <= x < y < |sorted| ==> string_comparison(sorted[x], sorted[y], 0)
{
    sorted := list;
    var n := |sorted|;
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant multiset(sorted) == multiset(list)
        invariant forall x, y :: 0 <= x < y < i ==> string_comparison(sorted[x], sorted[y], 0)
    {
        var j := i;
        while j > 0 && !string_comparison(sorted[j-1], sorted[j], 0)
            invariant 0 < j <= i
            invariant multiset(sorted) == multiset(old(sorted))
            invariant forall x, y :: 0 <= x < y < i && (x != j-1 || y != j) ==> string_comparison(old(sorted)[x], old(sorted)[y], 0)
            invariant forall k, l :: j <= k < l < i ==> string_comparison(sorted[k], sorted[l], 0)
            invariant 0 <= j-1 < |sorted|
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
    var i := 0;
    while i < |list|
        invariant 0 <= i <= |list|
        invariant forall k :: 0 <= k < |filtered_list| ==> |filtered_list[k]| % 2 == 0
        invariant multiset(filtered_list) <= multiset(list[0..i])
    {
        var s := list[i];
        if |s| % 2 == 0 {
            filtered_list := filtered_list + [s];
        }
        i := i + 1;
    }

    var sorted_filtered_list := insertion_sort_strings(filtered_list);

    sorted := [];
    var n := |sorted_filtered_list|;
    var k := 0;
    while k < n
        invariant 0 <= k <= n
        invariant |sorted| == k
        invariant forall x : int :: 0 <= x < k ==> |sorted[x]| % 2 == 0
        invariant (forall x, y : int :: 0 <= x < y < k ==> |sorted[x]| <= |sorted[y]|)
        invariant multiset(sorted) <= multiset(filtered_list)
        invariant multiset(sorted) == multiset(sorted_filtered_list[0..k])
        // The condition for the sorted output is on length, not string comparison.
        // We need to ensure that sorting by string comparison maintains the length-based sorting for elements with same length.
        // This is implicitly true as insertion_sort_strings maintains the order of elements if comparison returns false (i.e. elements are equal).
        // Since we are adding elements one by one from an already string-sorted list,
        // and only the length ordering is required for the final output, this loop simply constructs the final 'sorted' list.
    {
        var s_current := sorted_filtered_list[k];
        sorted := sorted + [s_current];
        k := k + 1;
    }
}
// </vc-code>


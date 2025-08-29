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
function compare_by_length(a: string, b: string): bool
{
    |a| < |b| || (|a| == |b| && comparison(a, b, 0))
}

lemma CompareByLengthTransitive(a: string, b: string, c: string)
    ensures compare_by_length(a, b) && compare_by_length(b, c) ==> compare_by_length(a, c)
{
    if compare_by_length(a, b) && compare_by_length(b, c) {
        if |a| < |b| && |b| < |c| {
            assert |a| < |c|;
        } else if |a| < |b| {
            assert |a| < |c|;
        } else if |b| < |c| {
            assert |a| < |c|;
        } else {
            assert |a| == |b| && |b| == |c|;
            assert comparison(a, b, 0) && comparison(b, c, 0);
            var i := 0;
            while i < |a|
                invariant 0 <= i <= |a|
                invariant forall k :: 0 <= k < i ==> a[k] == b[k]
                invariant forall k :: 0 <= k < i ==> b[k] == c[k]
            {
                if a[i] < c[i] {
                    assert comparison(a, c, 0);
                    return;
                } else if a[i] > c[i] {
                    assert !comparison(a, c, 0);
                    return;
                }
                i := i + 1;
            }
            assert comparison(a, c, 0);
        }
    }
}

lemma CompareByLengthTotal(a: string, b: string)
    ensures compare_by_length(a, b) || compare_by_length(b, a)
{
    if |a| < |b| {
        assert compare_by_length(a, b);
    } else if |b| < |a| {
        assert compare_by_length(b, a);
    } else {
        var i := 0;
        while i < |a|
            invariant 0 <= i <= |a|
            invariant forall k :: 0 <= k < i ==> a[k] == b[k]
        {
            if a[i] < b[i] {
                assert comparison(a, b, 0);
                assert compare_by_length(a, b);
                return;
            } else if a[i] > b[i] {
                assert !comparison(a, b, 0);
                assert compare_by_length(b, a);
                return;
            }
            i := i + 1;
        }
        assert comparison(a, b, 0);
        assert compare_by_length(a, b);
    }
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
method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
{
    sorted := list;
    var n := |list|;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |sorted| == |list|
        invariant multiset(sorted) == multiset(list)
        invariant forall k :: 0 <= k < i ==> forall m :: i <= m < n ==> compare_by_length(sorted[k], sorted[m]) || |sorted[k]| <= |sorted[m]|
        invariant forall k, m :: 0 <= k < m < i ==> |sorted[k]| <= |sorted[m]|
        invariant forall k :: 0 <= k < n ==> |sorted[k]| % 2 == 0
    {
        var min_idx := i;
        var j := i + 1;
        while j < n
            invariant i <= j <= n
            invariant i <= min_idx < n
            invariant forall k :: i <= k < j ==> compare_by_length(sorted[min_idx], sorted[k]) || (compare_by_length(sorted[k], sorted[min_idx]) ==> min_idx != k)
            invariant |sorted| == |list|
            invariant multiset(sorted) == multiset(list)
            invariant forall k :: 0 <= k < n ==> |sorted[k]| % 2 == 0
        {
            if compare_by_length(sorted[j], sorted[min_idx]) {
                min_idx := j;
            }
            j := j + 1;
        }
        if min_idx != i {
            sorted := sorted[i := sorted[min_idx]][min_idx := sorted[i]];
        }
        i := i + 1;
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
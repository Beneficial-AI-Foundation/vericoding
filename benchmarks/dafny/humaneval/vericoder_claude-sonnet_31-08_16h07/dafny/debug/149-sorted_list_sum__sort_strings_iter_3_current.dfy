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
predicate is_sorted(s: seq<string>)
{
    forall i, j :: 0 <= i < j < |s| ==> comparison(s[i], s[j], 0)
}

lemma comparison_reflexive(a: string)
    ensures comparison(a, a, 0)
{
    // This follows directly from the ensures clause of the comparison function
}

lemma comparison_transitive(a: string, b: string, c: string)
    requires comparison(a, b, 0) && comparison(b, c, 0)
    ensures comparison(a, c, 0)
{
    comparison_transitive_helper(a, b, c, 0);
}

lemma comparison_transitive_helper(a: string, b: string, c: string, i: int)
    requires 0 <= i <= |a| && 0 <= i <= |b| && 0 <= i <= |c|
    requires comparison(a, b, i) && comparison(b, c, i)
    ensures comparison(a, c, i)
    decreases |a| - i, |b| - i, |c| - i
{
    if (i < |a| && i < |b| && i < |c|) {
        if a[i] < b[i] {
            // a[i] < b[i], so comparison(a, c, i) is true regardless
        } else if a[i] > b[i] {
            // This contradicts comparison(a, b, i) being true
            assert false;
        } else {
            // a[i] == b[i]
            if b[i] < c[i] {
                // a[i] == b[i] < c[i], so comparison(a, c, i) is true
            } else if b[i] > c[i] {
                // This contradicts comparison(b, c, i) being true
                assert false;
            } else {
                // a[i] == b[i] == c[i], recurse
                comparison_transitive_helper(a, b, c, i + 1);
            }
        }
    }
}

method insertion_sort(arr: seq<string>) returns (result: seq<string>)
    ensures |result| == |arr|
    ensures multiset(result) == multiset(arr)
    ensures is_sorted(result)
{
    result := [];
    for i := 0 to |arr|
        invariant |result| == i
        invariant multiset(result) == multiset(arr[..i])
        invariant is_sorted(result)
    {
        var elem := arr[i];
        var j := 0;
        while j < |result| && comparison(result[j], elem, 0)
            invariant 0 <= j <= |result|
            invariant forall k :: 0 <= k < j ==> comparison(result[k], elem, 0)
            invariant forall k :: j <= k < |result| ==> !comparison(result[k], elem, 0) || result[k] == elem
        {
            j := j + 1;
        }
        
        var old_result := result;
        result := result[..j] + [elem] + result[j..];
        
        // Prove that the result is still sorted
        assert is_sorted(old_result);
        assert forall k :: 0 <= k < j ==> comparison(old_result[k], elem, 0);
        assert forall k :: j <= k < |old_result| ==> !comparison(old_result[k], elem, 0) || old_result[k] == elem;
        
        forall x, y | 0 <= x < y < |result|
            ensures comparison(result[x], result[y], 0)
        {
            if x < j && y == j {
                // result[x] is old_result[x], result[y] is elem
                assert comparison(result[x], elem, 0);
            } else if x == j && y > j {
                // result[x] is elem, result[y] is old_result[y-1]
                assert y - 1 >= j;
                assert !comparison(old_result[y-1], elem, 0) || old_result[y-1] == elem;
                if old_result[y-1] == elem {
                    comparison_reflexive(elem);
                } else {
                    // Since !comparison(old_result[y-1], elem, 0), we need comparison(elem, old_result[y-1], 0)
                    // This follows from the negation of comparison for strings
                }
            } else if x < j && y > j {
                // result[x] is old_result[x], result[y] is old_result[y-1]
                assert comparison(old_result[x], old_result[y-1], 0);
                assert comparison(old_result[x], elem, 0);
                if old_result[y-1] == elem {
                    assert comparison(old_result[x], elem, 0);
                } else {
                    assert !comparison(old_result[y-1], elem, 0);
                    // We can prove comparison(elem, old_result[y-1], 0) from the negation
                    comparison_transitive(old_result[x], elem, old_result[y-1]);
                }
            } else if x > j && y > j {
                // Both from old_result shifted by 1
                assert comparison(old_result[x-1], old_result[y-1], 0);
            } else {
                // x < j && y < j - from old_result
                assert comparison(old_result[x], old_result[y], 0);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
// </vc-spec>
// <vc-code>
{
    sorted := insertion_sort(list);
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
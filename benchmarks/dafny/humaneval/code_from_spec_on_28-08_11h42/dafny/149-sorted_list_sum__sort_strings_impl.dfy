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
lemma comparison_transitive(a: string, b: string, c: string, i: int)
    requires 0 <= i <= |a| && 0 <= i <= |b| && 0 <= i <= |c|
    ensures comparison(a, b, i) && comparison(b, c, i) ==> comparison(a, c, i)
{
    if comparison(a, b, i) && comparison(b, c, i) {
        comparison_transitive_helper(a, b, c, i);
    }
}

lemma comparison_transitive_helper(a: string, b: string, c: string, i: int)
    requires 0 <= i <= |a| && 0 <= i <= |b| && 0 <= i <= |c|
    requires comparison(a, b, i) && comparison(b, c, i)
    ensures comparison(a, c, i)
    decreases |a| - i, |b| - i, |c| - i
{
    if i < |a| && i < |b| && i < |c| {
        if a[i] < b[i] {
            assert comparison(a, c, i);
        } else if a[i] > b[i] {
            assert false;
        } else {
            if b[i] < c[i] {
                assert comparison(a, c, i);
            } else if b[i] > c[i] {
                assert false;
            } else {
                comparison_transitive_helper(a, b, c, i + 1);
            }
        }
    }
}

lemma comparison_antisymmetric(a: string, b: string, i: int)
    requires 0 <= i <= |a| && 0 <= i <= |b|
    ensures comparison(a, b, i) && comparison(b, a, i) ==> a == b
{
    if comparison(a, b, i) && comparison(b, a, i) {
        comparison_antisymmetric_helper(a, b, i);
    }
}

lemma comparison_antisymmetric_helper(a: string, b: string, i: int)
    requires 0 <= i <= |a| && 0 <= i <= |b|
    requires comparison(a, b, i) && comparison(b, a, i)
    ensures a == b
    decreases |a| - i, |b| - i
{
    if i < |a| && i < |b| {
        if a[i] != b[i] {
            assert false;
        } else {
            comparison_antisymmetric_helper(a, b, i + 1);
        }
    } else {
        assert |a| == |b|;
        if i == |a| && i == |b| {
            assert a == b;
        }
    }
}

lemma comparison_total(a: string, b: string, i: int)
    requires 0 <= i <= |a| && 0 <= i <= |b|
    ensures comparison(a, b, i) || comparison(b, a, i)
{
    comparison_total_helper(a, b, i);
}

lemma comparison_total_helper(a: string, b: string, i: int)
    requires 0 <= i <= |a| && 0 <= i <= |b|
    ensures comparison(a, b, i) || comparison(b, a, i)
    decreases |a| - i, |b| - i
{
    if i < |a| && i < |b| {
        if a[i] != b[i] {
            assert comparison(a, b, i) || comparison(b, a, i);
        } else {
            comparison_total_helper(a, b, i + 1);
        }
    }
}

lemma multiset_update_preservation(s: seq<string>, i: int, val: string)
    requires 0 <= i < |s|
    ensures multiset(s[i := val]) == multiset(s) - multiset{s[i]} + multiset{val}
{}

lemma comparison_reflexive(a: string, i: int)
    requires 0 <= i <= |a|
    ensures comparison(a, a, i)
    decreases |a| - i
{
    if i < |a| {
        comparison_reflexive(a, i + 1);
    }
}

method insertion_sort(arr: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |arr|
    ensures multiset(sorted) == multiset(arr)
    ensures forall x, y :: 0 <= x < y < |sorted| ==> comparison(sorted[x], sorted[y], 0)
{
    sorted := arr;
    if |sorted| <= 1 {
        return;
    }
    
    var i := 1;
    while i < |sorted|
        invariant 1 <= i <= |sorted|
        invariant |sorted| == |arr|
        invariant multiset(sorted) == multiset(arr)
        invariant forall x, y :: 0 <= x < y < i ==> comparison(sorted[x], sorted[y], 0)
    {
        var key := sorted[i];
        var j := i - 1;
        var old_sorted := sorted;
        
        while j >= 0 && !comparison(sorted[j], key, 0)
            invariant -1 <= j < i
            invariant |sorted| == |arr|
            invariant multiset(sorted) == multiset(old_sorted)
            invariant forall k :: 0 <= k <= j ==> sorted[k] == old_sorted[k]
            invariant forall k :: j + 2 <= k < i ==> sorted[k] == old_sorted[k-1]
            invariant j >= 0 ==> sorted[j + 1] == old_sorted[j]
            invariant sorted[i] == key
            invariant forall k :: i < k < |sorted| ==> sorted[k] == old_sorted[k]
            invariant forall x, y :: 0 <= x < y <= j ==> comparison(sorted[x], sorted[y], 0)
            invariant forall k :: j + 1 < k < i ==> sorted[k] == old_sorted[k-1]
        {
            comparison_total(sorted[j], key, 0);
            sorted := sorted[j + 1 := sorted[j]];
            j := j - 1;
        }
        
        sorted := sorted[j + 1 := key];
        
        forall x, y | 0 <= x < y < i + 1 
            ensures comparison(sorted[x], sorted[y], 0)
        {
            if y == j + 1 {
                if x <= j {
                    comparison_total(sorted[x], key, 0);
                }
            } else if x == j + 1 {
                if j >= 0 {
                    comparison_total(key, sorted[y], 0);
                } else {
                    comparison_reflexive(key, 0);
                }
            }
        }
        
        i := i + 1;
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
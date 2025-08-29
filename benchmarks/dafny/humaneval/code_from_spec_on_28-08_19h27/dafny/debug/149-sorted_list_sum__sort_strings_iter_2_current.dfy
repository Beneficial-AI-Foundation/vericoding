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
predicate is_sorted_by_comparison(s: seq<string>)
{
    forall i, j :: 0 <= i < j < |s| ==> comparison(s[i], s[j], 0)
}

lemma comparison_reflexive(a: string)
    ensures comparison(a, a, 0)
{
    // This follows from the ensures clause of comparison function
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
    decreases |a| - i
{
    if i < |a| && i < |b| && i < |c| {
        if a[i] < b[i] {
            // a[i] < b[i], so comparison(a, c, i) is true
        } else if a[i] > b[i] {
            // This contradicts comparison(a, b, i)
            assert false;
        } else {
            // a[i] == b[i]
            if b[i] < c[i] {
                // a[i] == b[i] < c[i], so comparison(a, c, i) is true
            } else if b[i] > c[i] {
                // This contradicts comparison(b, c, i)
                assert false;
            } else {
                // a[i] == b[i] == c[i]
                comparison_transitive_helper(a, b, c, i + 1);
            }
        }
    }
}

lemma insertion_preserves_sorted(sorted: seq<string>, j: int)
    requires 0 < j < |sorted|
    requires forall x, y :: 0 <= x < y < j ==> comparison(sorted[x], sorted[y], 0)
    requires forall x, y :: j < x < y < |sorted| ==> comparison(sorted[x], sorted[y], 0)
    requires forall x, y :: 0 <= x < j && j < y < |sorted| ==> comparison(sorted[x], sorted[y], 0)
    requires !comparison(sorted[j-1], sorted[j], 0)
    ensures var new_sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
        forall x, y :: 0 <= x < y < j ==> comparison(new_sorted[x], new_sorted[y], 0)
{
    var new_sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
    forall x, y | 0 <= x < y < j
        ensures comparison(new_sorted[x], new_sorted[y], 0)
    {
        if x == j-1 && y == j {
            // This case is excluded since y < j
            assert false;
        } else if x == j-1 {
            // new_sorted[x] = sorted[j], new_sorted[y] = sorted[y]
            // We need comparison(sorted[j], sorted[y], 0)
            // This follows from the invariant for j < y
        } else if y == j-1 {
            // This case is excluded since y < j and j-1 < j
            assert false;
        } else {
            // Neither x nor y is j-1, so new_sorted[x] = sorted[x] and new_sorted[y] = sorted[y]
            assert comparison(new_sorted[x], new_sorted[y], 0);
        }
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method sort_strings(list: seq<string>) returns (sorted: seq<string>)
Sort elements. Ensures: returns the correct size/count; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures is_sorted_by_comparison(sorted)
// </vc-spec>
// <vc-code>
{
    sorted := list;
    var n := |sorted|;
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |sorted| == n == |list|
        invariant multiset(sorted) == multiset(list)
        invariant forall x, y :: 0 <= x < y < i ==> comparison(sorted[x], sorted[y], 0)
    {
        var j := i;
        while j > 0 && !comparison(sorted[j-1], sorted[j], 0)
            invariant 0 <= j <= i < n
            invariant |sorted| == n
            invariant multiset(sorted) == multiset(list)
            invariant forall x, y :: 0 <= x < y < j ==> comparison(sorted[x], sorted[y], 0)
            invariant forall x, y :: j < x < y <= i ==> comparison(sorted[x], sorted[y], 0)
            invariant forall x, y :: 0 <= x < j && j < y <= i ==> comparison(sorted[x], sorted[y], 0)
            invariant j < i ==> comparison(sorted[j], sorted[j+1], 0)
        {
            insertion_preserves_sorted(sorted, j);
            sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
            j := j - 1;
        }
        i := i + 1;
    }
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
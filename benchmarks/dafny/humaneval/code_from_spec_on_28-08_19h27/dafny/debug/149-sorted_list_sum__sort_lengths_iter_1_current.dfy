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
predicate IsSortedByLength(s: seq<string>)
{
    forall i, j :: 0 <= i < j < |s| ==> |s[i]| <= |s[j]|
}

lemma SortedByLengthTransitive(s: seq<string>)
    requires IsSortedByLength(s)
    ensures forall i, j :: 0 <= i <= j < |s| ==> |s[i]| <= |s[j]|
{
    // Proof by induction on the difference j - i
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
Sort elements. Requires: the condition holds for all values. Ensures: the result is sorted according to the ordering relation; returns the correct size/count; returns a sorted permutation of the input; the result is sorted according to the ordering relation.
*/
// </vc-description>

// <vc-spec>
method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures IsSortedByLength(sorted)
    ensures forall i, j :: 0 <= i < j < |sorted| ==> |sorted[i]| <= |sorted[j]|
// </vc-spec>
// <vc-code>
{
    sorted := list;
    var n := |sorted|;
    
    // Bubble sort by string length
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |sorted| == n == |list|
        invariant multiset(sorted) == multiset(list)
        invariant forall x, y :: 0 <= x < y < i ==> |sorted[x]| <= |sorted[y]|
    {
        var j := 0;
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
            invariant |sorted| == n == |list|
            invariant multiset(sorted) == multiset(list)
            invariant forall x, y :: 0 <= x < y < n - 1 - i - j ==> |sorted[x]| <= |sorted[y]| || (x < j)
        {
            if |sorted[j]| > |sorted[j + 1]| {
                var temp := sorted[j];
                sorted := sorted[j := sorted[j + 1]][j + 1 := temp];
            }
            j := j + 1;
        }
        i := i + 1;
    }
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
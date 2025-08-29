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

predicate PartiallyBubbleSorted(s: seq<string>, i: int)
    requires 0 <= i <= |s|
{
    forall x, y :: 0 <= x < y < i ==> |s[x]| <= |s[y]|
}

lemma SwapPreservesMultiset(s: seq<string>, i: int, j: int)
    requires 0 <= i < |s| && 0 <= j < |s|
    ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
    // Multiset is preserved by swapping elements
}

lemma BubbleSortMaintainsInvariant(s: seq<string>, i: int, j: int)
    requires 0 <= i < |s|
    requires 0 <= j < |s| - 1 - i
    requires PartiallyBubbleSorted(s, i)
    requires forall k :: 0 <= k < j ==> |s[k]| <= |s[k+1]|
    requires |s[j]| > |s[j+1]|
    ensures PartiallyBubbleSorted(s[j := s[j+1]][j+1 := s[j]], i)
{
    var s' := s[j := s[j+1]][j+1 := s[j]];
    forall x, y | 0 <= x < y < i
        ensures |s'[x]| <= |s'[y]|
    {
        if x == j || x == j+1 || y == j || y == j+1 {
            if x == j && y == j+1 {
                assert |s'[x]| == |s[j+1]| <= |s[j]| == |s'[y]|;
            } else if x != j && x != j+1 && y != j && y != j+1 {
                assert |s'[x]| == |s[x]| <= |s[y]| == |s'[y]|;
            }
        } else {
            assert |s'[x]| == |s[x]| <= |s[y]| == |s'[y]|;
        }
    }
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
        invariant forall k :: 0 <= k < i ==> forall l :: i <= l < |sorted| ==> |sorted[k]| <= |sorted[l]|
    {
        var j := 0;
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
            invariant |sorted| == n == |list|
            invariant multiset(sorted) == multiset(list)
            invariant forall x, y :: 0 <= x < y < i ==> |sorted[x]| <= |sorted[y]|
            invariant forall k :: 0 <= k < i ==> forall l :: i <= l < |sorted| ==> |sorted[k]| <= |sorted[l]|
            invariant forall k :: 0 <= k < j ==> |sorted[k]| <= |sorted[k+1]|
            invariant j == 0 || forall k :: j <= k < n - i ==> |sorted[j-1]| <= |sorted[k]|
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
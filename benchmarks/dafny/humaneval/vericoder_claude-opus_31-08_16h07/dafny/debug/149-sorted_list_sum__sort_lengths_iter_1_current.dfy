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
lemma MultisetPreservedBySwap(s: seq<string>, i: int, j: int)
    requires 0 <= i < |s| && 0 <= j < |s| && i != j
    ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
    var s' := s[i := s[j]][j := s[i]];
    assert s'[i] == s[j] && s'[j] == s[i];
    assert forall k :: 0 <= k < |s'| && k != i && k != j ==> s'[k] == s[k];
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
{
    sorted := list;
    var n := |sorted|;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |sorted| == |list|
        invariant multiset(sorted) == multiset(list)
        invariant forall k : int :: 0 <= k < |sorted| ==> |sorted[k]| % 2 == 0
        invariant forall x, y :: i <= x < y < n ==> |sorted[x]| <= |sorted[y]|
        invariant forall x, y :: 0 <= x < i && i <= y < n ==> |sorted[x]| <= |sorted[y]|
    {
        var j := i + 1;
        var minIdx := i;
        
        while j < n
            invariant i < j <= n
            invariant i <= minIdx < j
            invariant forall k :: i <= k < j ==> |sorted[minIdx]| <= |sorted[k]|
        {
            if |sorted[j]| < |sorted[minIdx]| {
                minIdx := j;
            }
            j := j + 1;
        }
        
        if minIdx != i {
            MultisetPreservedBySwap(sorted, i, minIdx);
            var temp := sorted[i];
            sorted := sorted[i := sorted[minIdx]];
            sorted := sorted[minIdx := temp];
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
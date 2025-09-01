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
predicate sorted_by_length(sorted: seq<string>)
{
    forall x: int, y: int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
}

lemma MultisetSliceSubset(list: seq<string>, i: int)
    requires 0 <= i <= |list|
    ensures multiset(list[0..i]) <= multiset(list)
{
}

lemma MultisetConcatLemma<T>(s1: seq<T>, s2: seq<T>)
    ensures multiset(s1 + s2) == multiset(s1) + multiset(s2)
{
}

lemma MultisetAppendLemma<T>(s: seq<T>, e: T)
    ensures multiset(s + [e]) == multiset(s) + multiset([e])
{
}

lemma MultisetAppendSeqLemma<T>(s: seq<T>, e: seq<T>)
    ensures multiset(s + e) == multiset(s) + multiset(e)
{
}

lemma SortedInsertMaintainsOrder(filtered: seq<string>, pos: int, elem: string)
    requires sorted_by_length(filtered)
    requires forall k :: 0 <= k < pos ==> |filtered[k]| <= |elem|
    requires forall k :: pos <= k < |filtered| ==> |elem| <= |filtered[k]|
    ensures sorted_by_length(filtered[0..pos] + [elem] + filtered[pos..])
{
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
    var filtered: seq<string> := [];
    var i := 0;
    
    while i < |list|
        invariant 0 <= i <= |list|
        invariant |filtered| <= i
        invariant forall j :: 0 <= j < |filtered| ==> |filtered[j]| % 2 == 0
        invariant multiset(filtered) <= multiset(list[0..i])
        invariant sorted_by_length(filtered)
    {
        MultisetSliceSubset(list, i);
        if |list[i]| % 2 == 0 {
            if |filtered| == 0 {
                filtered := [list[i]];
                assert multiset(filtered) == multiset([list[i]]);
                assert multiset([list[i]]) <= multiset(list[0..i+1]);
            } else {
                var pos := |filtered|;
                var j := 0;
                while j < |filtered| && |filtered[j]| <= |list[i]|
                    invariant 0 <= j <= |filtered|
                    invariant forall k :: 0 <= k < j ==> |filtered[k]| <= |list[i]|
                {
                    j := j + 1;
                }
                pos := j;
                
                var newFiltered := filtered[0..pos] + [list[i]] + filtered[pos..];
                MultisetConcatLemma(filtered[0..pos], [list[i]] + filtered[pos..]);
                MultisetAppendSeqLemma([list[i]], filtered[pos..]);
                MultisetConcatLemma(filtered[0..pos] + [list[i]], filtered[pos..]);
                assert multiset(newFiltered) == multiset(filtered) + multiset([list[i]]);
                assert multiset(newFiltered) <= multiset(list[0..i]) + multiset([list[i]]);
                assert multiset(list[0..i]) + multiset([list[i]]) == multiset(list[0..i+1]);
                
                ghost var elem := list[i];
                assert forall k :: pos <= k < |filtered| ==> |elem| <= |filtered[k]|;
                SortedInsertMaintainsOrder(filtered, pos, elem);
                filtered := newFiltered;
            }
        }
        i := i + 1;
    }
    
    sorted := filtered;
}
// </vc-code>


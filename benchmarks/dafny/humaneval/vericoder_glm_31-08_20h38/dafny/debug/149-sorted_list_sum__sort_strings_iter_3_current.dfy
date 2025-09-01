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

function strings_lex_order(a: string, b: string): bool {
    comparison(a, b, 0)
}
// </vc-helpers>

// <vc-spec>
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
// </vc-spec>
// <vc-code>
{
    if (|list| <= 1) {
        sorted := list;
    } else {
        var pivot_idx := 0;
        var pivot := list[pivot_idx];
        var less, equal, greater : seq<string> := [], [], [];
        
        for i := 0 to |list|
            invariant multiset(less + equal + greater) == multiset(list[0..i])
            invariant |less| + |equal| + |greater| == i
        {
            if i == pivot_idx {
                equal := equal + [list[i]];
            } else if strings_lex_order(list[i], pivot) {
                less := less + [list[i]];
            } else {
                greater := greater + [list[i]];
            }
        }
        
        var sorted_less := sort_strings(less);
        var sorted_greater := sort_strings(greater);
        
        assert |sorted_less| == |less|;
        assert |sorted_greater| == |greater|;
        assert multiset(sorted_less) == multiset(less);
        assert multiset(sorted_greater) == multiset(greater);
        assert multiset(sorted_less) + multiset(equal) + multiset(sorted_greater) == multiset(less) + multiset(equal) + multiset(greater);
        assert multiset(less) + multiset(equal) + multiset(greater) == multiset(list);
        
        sorted := sorted_less + equal + sorted_greater;
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
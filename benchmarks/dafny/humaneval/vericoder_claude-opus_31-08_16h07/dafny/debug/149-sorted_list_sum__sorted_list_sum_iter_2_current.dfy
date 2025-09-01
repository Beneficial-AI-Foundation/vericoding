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
function filter_even_length(list: seq<string>): seq<string>
    ensures |filter_even_length(list)| <= |list|
    ensures forall i : int :: 0 <= i < |filter_even_length(list)| ==> |filter_even_length(list)[i]| % 2 == 0
    ensures multiset(filter_even_length(list)) <= multiset(list)
{
    if |list| == 0 then
        []
    else if |list[0]| % 2 == 0 then
        assert multiset(filter_even_length(list[1..])) <= multiset(list[1..]);
        assert multiset([list[0]]) + multiset(filter_even_length(list[1..])) <= multiset([list[0]]) + multiset(list[1..]);
        assert multiset([list[0]]) + multiset(list[1..]) == multiset(list);
        [list[0]] + filter_even_length(list[1..])
    else
        assert multiset(filter_even_length(list[1..])) <= multiset(list[1..]);
        assert multiset(list[1..]) <= multiset(list);
        filter_even_length(list[1..])
}

lemma filter_even_length_preserves_evenness(list: seq<string>)
    ensures forall i : int :: 0 <= i < |filter_even_length(list)| ==> |filter_even_length(list)[i]| % 2 == 0
{
    // This follows directly from the ensures clause of filter_even_length
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
    var filtered := [];
    var i := 0;
    
    while i < |list|
        invariant 0 <= i <= |list|
        invariant |filtered| <= i
        invariant forall j : int :: 0 <= j < |filtered| ==> |filtered[j]| % 2 == 0
        invariant multiset(filtered) <= multiset(list[..i])
        invariant multiset(filtered) <= multiset(list)
    {
        if |list[i]| % 2 == 0 {
            assert list[..i+1] == list[..i] + [list[i]];
            assert multiset(list[..i+1]) == multiset(list[..i]) + multiset([list[i]]);
            filtered := filtered + [list[i]];
            assert multiset(filtered) == multiset(filtered[..|filtered|-1]) + multiset([list[i]]);
        }
        assert list[..i+1] == list[..i] + [list[i]];
        i := i + 1;
    }
    
    assert list[..|list|] == list;
    sorted := sort_lengths(filtered);
}
// </vc-code>


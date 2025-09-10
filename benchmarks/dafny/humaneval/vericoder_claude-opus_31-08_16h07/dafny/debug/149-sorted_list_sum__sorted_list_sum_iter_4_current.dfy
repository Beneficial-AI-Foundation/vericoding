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
        var rest := filter_even_length(list[1..]);
        assert multiset(rest) <= multiset(list[1..]);
        assert list == [list[0]] + list[1..];
        assert multiset(list) == multiset([list[0]]) + multiset(list[1..]);
        assert multiset([list[0]] + rest) == multiset([list[0]]) + multiset(rest);
        [list[0]] + rest
    else
        var rest := filter_even_length(list[1..]);
        assert multiset(rest) <= multiset(list[1..]);
        assert list == [list[0]] + list[1..];
        assert multiset(list) == multiset([list[0]]) + multiset(list[1..]);
        rest
}

lemma filter_even_length_preserves_evenness(list: seq<string>)
    ensures forall i : int :: 0 <= i < |filter_even_length(list)| ==> |filter_even_length(list)[i]| % 2 == 0
{
    // This follows directly from the ensures clause of filter_even_length
}

lemma multiset_slice_property(s: seq<string>, i: int)
    requires 0 <= i < |s|
    ensures multiset(s[..i+1]) == multiset(s[..i]) + multiset([s[i]])
{
    assert s[..i+1] == s[..i] + [s[i]];
}

lemma multiset_append_single(s: seq<string>, x: string)
    ensures multiset(s + [x]) == multiset(s) + multiset([x])
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
    var filtered := [];
    var i := 0;
    
    while i < |list|
        invariant 0 <= i <= |list|
        invariant |filtered| <= i
        invariant forall j : int :: 0 <= j < |filtered| ==> |filtered[j]| % 2 == 0
        invariant multiset(filtered) <= multiset(list[..i])
    {
        if |list[i]| % 2 == 0 {
            multiset_slice_property(list, i);
            multiset_append_single(filtered, list[i]);
            filtered := filtered + [list[i]];
            assert multiset(filtered) <= multiset(list[..i+1]);
        }
        i := i + 1;
    }
    
    assert list[..|list|] == list;
    assert multiset(filtered) <= multiset(list);
    sorted := sort_lengths(filtered);
}
// </vc-code>


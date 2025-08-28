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
function filter_even_lengths(list: seq<string>): seq<string>
{
    if |list| == 0 then []
    else if |list[0]| % 2 == 0 then [list[0]] + filter_even_lengths(list[1..])
    else filter_even_lengths(list[1..])
}

lemma filter_even_lengths_properties(list: seq<string>)
    ensures forall i :: 0 <= i < |filter_even_lengths(list)| ==> |filter_even_lengths(list)[i]| % 2 == 0
    ensures multiset(filter_even_lengths(list)) <= multiset(list)
    ensures |filter_even_lengths(list)| <= |list|
{
    if |list| == 0 {
    } else if |list[0]| % 2 == 0 {
        filter_even_lengths_properties(list[1..]);
        assert filter_even_lengths(list) == [list[0]] + filter_even_lengths(list[1..]);
        assert multiset([list[0]] + filter_even_lengths(list[1..])) == multiset([list[0]]) + multiset(filter_even_lengths(list[1..]));
        assert multiset(filter_even_lengths(list[1..])) <= multiset(list[1..]);
        assert multiset([list[0]]) + multiset(filter_even_lengths(list[1..])) <= multiset([list[0]]) + multiset(list[1..]);
        assert list == [list[0]] + list[1..];
        assert multiset(list) == multiset([list[0]] + list[1..]);
        assert multiset([list[0]] + list[1..]) == multiset([list[0]]) + multiset(list[1..]);
    } else {
        filter_even_lengths_properties(list[1..]);
        assert multiset(filter_even_lengths(list)) == multiset(filter_even_lengths(list[1..]));
        assert multiset(filter_even_lengths(list[1..])) <= multiset(list[1..]);
        assert list == [list[0]] + list[1..];
        assert multiset(list) == multiset([list[0]]) + multiset(list[1..]);
        assert multiset(list[1..]) <= multiset(list);
    }
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
    var filtered := filter_even_lengths(list);
    filter_even_lengths_properties(list);
    
    if |filtered| == 0 {
        sorted := [];
        return;
    }
    
    sorted := sort_lengths(filtered);
    assert multiset(sorted) == multiset(filtered);
    assert multiset(filtered) <= multiset(list);
    assert multiset(sorted) <= multiset(list);
}
// </vc-code>

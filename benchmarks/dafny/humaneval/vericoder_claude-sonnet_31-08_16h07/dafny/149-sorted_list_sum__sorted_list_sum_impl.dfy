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
lemma filter_even_lengths_preserves_even(list: seq<string>, filtered: seq<string>)
    requires forall i :: 0 <= i < |filtered| ==> exists j :: 0 <= j < |list| && filtered[i] == list[j] && |list[j]| % 2 == 0
    ensures forall i : int :: 0 <= i < |filtered| ==> |filtered[i]| % 2 == 0
{
}

lemma filter_even_lengths_multiset_property(list: seq<string>, filtered: seq<string>)
    requires forall i :: 0 <= i < |filtered| ==> exists j :: 0 <= j < |list| && filtered[i] == list[j]
    ensures multiset(filtered) <= multiset(list)
{
    if |filtered| == 0 {
        return;
    }
    
    var head := filtered[0];
    var tail := filtered[1..];
    
    assert head in multiset(list);
    filter_even_lengths_multiset_property(list, tail);
    assert multiset(tail) <= multiset(list);
    assert multiset(filtered) == multiset([head]) + multiset(tail);
}

lemma append_preserves_multiset_inclusion(list: seq<string>, filtered_seq: seq<string>, element: string)
    requires multiset(filtered_seq) <= multiset(list)
    requires element in list
    ensures multiset(filtered_seq + [element]) <= multiset(list)
{
    assert multiset(filtered_seq + [element]) == multiset(filtered_seq) + multiset([element]);
    assert multiset([element]) <= multiset(list);
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
    var filtered_seq := [];
    
    for i := 0 to |list|
        invariant 0 <= i <= |list|
        invariant forall j :: 0 <= j < |filtered_seq| ==> |filtered_seq[j]| % 2 == 0
        invariant forall j :: 0 <= j < |filtered_seq| ==> exists k :: 0 <= k < |list| && filtered_seq[j] == list[k]
        invariant multiset(filtered_seq) <= multiset(list)
    {
        if |list[i]| % 2 == 0 {
            append_preserves_multiset_inclusion(list, filtered_seq, list[i]);
            filtered_seq := filtered_seq + [list[i]];
        }
    }
    
    if |filtered_seq| == 0 {
        return [];
    }
    
    filter_even_lengths_preserves_even(list, filtered_seq);
    filter_even_lengths_multiset_property(list, filtered_seq);
    sorted := sort_lengths(filtered_seq);
}
// </vc-code>


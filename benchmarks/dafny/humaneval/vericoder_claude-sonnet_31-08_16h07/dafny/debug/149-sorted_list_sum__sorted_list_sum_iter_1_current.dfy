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
    requires filtered == seq(i | 0 <= i < |list| && |list[i]| % 2 == 0 :: list[i])
    ensures forall i : int :: 0 <= i < |filtered| ==> |filtered[i]| % 2 == 0
{
}

lemma filter_even_lengths_multiset_property(list: seq<string>, filtered: seq<string>)
    requires filtered == seq(i | 0 <= i < |list| && |list[i]| % 2 == 0 :: list[i])
    ensures multiset(filtered) <= multiset(list)
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
    var filtered := seq(i | 0 <= i < |list| && |list[i]| % 2 == 0 :: list[i]);
    
    if |filtered| == 0 {
        return [];
    }
    
    filter_even_lengths_preserves_even(list, filtered);
    filter_even_lengths_multiset_property(list, filtered);
    
    sorted := sort_lengths(filtered);
}
// </vc-code>


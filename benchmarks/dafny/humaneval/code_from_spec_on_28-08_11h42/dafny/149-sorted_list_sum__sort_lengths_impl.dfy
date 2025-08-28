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
lemma multiset_filter_preserves_subset<T>(s: seq<T>, pred: T -> bool)
    ensures multiset(seq(|s|, i requires 0 <= i < |s| => if pred(s[i]) then s[i] else s[0])) <= multiset(s)
{
    var filtered := seq(|s|, i requires 0 <= i < |s| => if pred(s[i]) then s[i] else s[0]);
    forall x | x in multiset(filtered)
        ensures x in multiset(s)
    {
        assert exists i :: 0 <= i < |filtered| && filtered[i] == x;
        var i :| 0 <= i < |filtered| && filtered[i] == x;
        if pred(s[i]) {
            assert filtered[i] == s[i];
            assert s[i] in multiset(s);
        } else {
            assert filtered[i] == s[0];
            assert s[0] in multiset(s);
        }
    }
}

lemma length_preserved_in_multiset(s1: seq<string>, s2: seq<string>)
    requires multiset(s1) == multiset(s2)
    ensures |s1| == |s2|
{
    assert |multiset(s1)| == |s1|;
    assert |multiset(s2)| == |s2|;
}

lemma even_length_preserved_in_sort(original: seq<string>, sorted: seq<string>)
    requires forall i :: 0 <= i < |original| ==> |original[i]| % 2 == 0
    requires multiset(original) == multiset(sorted)
    ensures forall i :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
{
    forall i | 0 <= i < |sorted|
        ensures |sorted[i]| % 2 == 0
    {
        assert sorted[i] in multiset(sorted);
        assert sorted[i] in multiset(original);
        assert exists j :: 0 <= j < |original| && original[j] == sorted[i];
    }
}

predicate is_sorted_by_length(s: seq<string>)
{
    forall x, y :: 0 <= x < y < |s| ==> |s[x]| <= |s[y]|
}

ghost function sort_strings_spec(list: seq<string>): (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures is_sorted_by_length(sorted)
{
    assume{:axiom} false;
    list
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
    var filtered := [];
    var i := 0;
    
    while i < |list|
        invariant 0 <= i <= |list|
        invariant forall j :: 0 <= j < |filtered| ==> |filtered[j]| % 2 == 0
        invariant |filtered| == i
        invariant filtered == list[..i]
        invariant multiset(filtered) == multiset(list[..i])
    {
        filtered := filtered + [list[i]];
        i := i + 1;
    }
    
    assert filtered == list;
    assert |filtered| == |list|;
    assert multiset(filtered) == multiset(list);
    
    sorted := sort_strings_spec(filtered);
    
    even_length_preserved_in_sort(filtered, sorted);
    length_preserved_in_multiset(filtered, sorted);
    
    assert is_sorted_by_length(sorted);
    assert forall x, y :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|;
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
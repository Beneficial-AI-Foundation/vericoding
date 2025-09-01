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
lemma multiset_filter_subset(s: seq<string>, p: string -> bool)
    ensures multiset(filter(s, p)) <= multiset(s)
{
    if |s| == 0 {
    } else {
        multiset_filter_subset(s[1..], p);
    }
}

function filter(s: seq<string>, p: string -> bool): seq<string>
{
    if |s| == 0 then []
    else if p(s[0]) then [s[0]] + filter(s[1..], p)
    else filter(s[1..], p)
}

lemma filter_preserves_property(s: seq<string>)
    requires forall i :: 0 <= i < |s| ==> |s[i]| % 2 == 0
    ensures forall i :: 0 <= i < |filter(s, x => |x| % 2 == 0)| ==> |filter(s, x => |x| % 2 == 0)[i]| % 2 == 0
{
    if |s| == 0 {
    } else {
        filter_preserves_property(s[1..]);
    }
}

lemma filter_same_when_all_satisfy(s: seq<string>)
    requires forall i :: 0 <= i < |s| ==> |s[i]| % 2 == 0
    ensures filter(s, x => |x| % 2 == 0) == s
    ensures multiset(filter(s, x => |x| % 2 == 0)) == multiset(s)
{
    if |s| == 0 {
    } else {
        filter_same_when_all_satisfy(s[1..]);
    }
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
    var filtered := filter(list, x => |x| % 2 == 0);
    filter_same_when_all_satisfy(list);
    assert filtered == list;
    assert multiset(filtered) == multiset(list);
    sorted := sort_strings(filtered);
    assert |sorted| == |filtered|;
    assert |sorted| == |list|;
    assert multiset(sorted) == multiset(filtered);
    assert multiset(sorted) == multiset(list);
    assert forall i :: 0 <= i < |sorted| ==> sorted[i] in multiset(list);
    assert forall i :: 0 <= i < |list| ==> |list[i]| % 2 == 0;
    assert forall i :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0;
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
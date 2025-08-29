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
lemma comparison_is_length_order(a: string, b: string)
    requires |a| % 2 == 0 && |b| % 2 == 0
    requires |a| <= |b|
    ensures comparison(a, b, 0)
{
    if |a| < |b| {
        if |a| == 0 {
            assert comparison(a, b, 0);
        } else {
            comparison_helper(a, b, 0);
        }
    } else {
        assert |a| == |b|;
        comparison_equal_length(a, b, 0);
    }
}

lemma comparison_helper(a: string, b: string, i: int)
    requires 0 <= i < |a| < |b|
    requires |a| % 2 == 0 && |b| % 2 == 0
    ensures comparison(a, b, i)
    decreases |a| - i
{
    if i < |a| && i < |b| {
        if a[i] < b[i] {
            assert comparison(a, b, i);
        } else if a[i] > b[i] {
            assert comparison(a, b, i) == false;
            assert false;
        } else {
            comparison_helper(a, b, i + 1);
        }
    } else {
        assert i >= |a|;
        assert |a| <= |b|;
        assert comparison(a, b, i);
    }
}

lemma comparison_equal_length(a: string, b: string, i: int)
    requires 0 <= i <= |a| == |b|
    ensures comparison(a, b, i)
    decreases |a| - i
{
    if i < |a| && i < |b| {
        if a[i] < b[i] {
            assert comparison(a, b, i);
        } else if a[i] > b[i] {
            assert comparison(a, b, i);
        } else {
            comparison_equal_length(a, b, i + 1);
        }
    } else {
        assert |a| <= |b|;
        assert comparison(a, b, i);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
Sort elements. Requires: requires size of listsize of  > 0. Ensures: the size is bounded; the result is sorted according to the ordering relation; the result is sorted according to the ordering relation; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures multiset(sorted) <= multiset(list)
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> comparison(sorted[x], sorted[y], 0)
// </vc-spec>
// <vc-code>
{
    var even_strings := [];
    var i := 0;
    while i < |list|
        invariant 0 <= i <= |list|
        invariant forall j : int :: 0 <= j < |even_strings| ==> |even_strings[j]| % 2 == 0
        invariant multiset(even_strings) <= multiset(list)
    {
        if |list[i]| % 2 == 0 {
            even_strings := even_strings + [list[i]];
        }
        i := i + 1;
    }
    
    if |even_strings| == 0 {
        sorted := [];
    } else {
        sorted := sort_lengths(even_strings);
        
        forall x, y | 0 <= x < y < |sorted|
            ensures comparison(sorted[x], sorted[y], 0)
        {
            comparison_is_length_order(sorted[x], sorted[y]);
        }
    }
}
// </vc-code>

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
predicate is_sorted(s: seq<string>)
{
    forall i, j :: 0 <= i < j < |s| ==> comparison(s[i], s[j], 0)
}

lemma comparison_reflexive(a: string)
    ensures comparison(a, a, 0)
{
    comparison_reflexive_helper(a, a, 0);
}

lemma comparison_reflexive_helper(a: string, b: string, i: int)
    requires a == b
    requires 0 <= i <= |a| && 0 <= i <= |b|
    ensures comparison(a, b, i)
    decreases |a| - i
{
    if (i < |a| && i < |b|) {
        if a[i] == b[i] {
            comparison_reflexive_helper(a, b, i + 1);
        }
    }
}

lemma comparison_transitive(a: string, b: string, c: string)
    requires comparison(a, b, 0) && comparison(b, c, 0)
    ensures comparison(a, c, 0)
{
    comparison_transitive_helper(a, b, c, 0);
}

lemma comparison_transitive_helper(a: string, b: string, c: string, i: int)
    requires comparison(a, b, i) && comparison(b, c, i)
    requires 0 <= i <= |a| && 0 <= i <= |b| && 0 <= i <= |c|
    ensures comparison(a, c, i)
    decreases |a| - i, |b| - i, |c| - i
{
}

method insertion_sort(arr: seq<string>) returns (result: seq<string>)
    ensures |result| == |arr|
    ensures multiset(result) == multiset(arr)
    ensures is_sorted(result)
{
    result := [];
    for i := 0 to |arr|
        invariant |result| == i
        invariant multiset(result) == multiset(arr[..i])
        invariant is_sorted(result)
    {
        var elem := arr[i];
        var j := 0;
        while j < |result| && comparison(result[j], elem, 0)
            invariant 0 <= j <= |result|
            invariant forall k :: 0 <= k < j ==> comparison(result[k], elem, 0)
        {
            j := j + 1;
        }
        result := result[..j] + [elem] + result[j..];
        comparison_reflexive(elem);
    }
}
// </vc-helpers>

// <vc-spec>
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
// </vc-spec>
// <vc-code>
{
    sorted := insertion_sort(list);
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
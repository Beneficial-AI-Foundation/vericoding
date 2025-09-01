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
function IsSortedByLength(s: seq<string>): bool
{
    forall i, j :: 0 <= i < j < |s| ==> |s[i]| <= |s[j]|
}

predicate IsPermutation<T>(s1: seq<T>, s2: seq<T>)
{
    multiset(s1) == multiset(s2)
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
    var n := |list|;
    if n == 0 {
        return list;
    }

    var arr := new string[n];
    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> arr[k] == list[k]
        invariant IsPermutation(arr[0..i], list[0..i])
        invariant forall x :: 0 <= x < i ==> |arr[x]| % 2 == 0
    {
        arr[i] := list[i];
    }

    for i := 1 to n - 1
        invariant 1 <= i <= n
        invariant IsPermutation(arr[0..i] + arr[i..n], list)
        invariant forall k, l :: 0 <= k < l < i ==> |arr[k]| <= |arr[l]|
        invariant forall x :: 0 <= x < n ==> |arr[x]| % 2 == 0
    {
        var key := arr[i];
        var j := i - 1;
        
        while j >= 0 && |arr[j]| > |key|
            invariant -1 <= j < i
            invariant forall k :: j < k < i ==> |arr[k]| >= |key|
            invariant IsPermutation(arr[0..j+1] + arr[j+2..i+1], old(arr[0..i+1]))
            invariant forall k :: 0 <= k < j+1 ==> arr[k] == old(arr[k])
            invariant forall x :: 0 <= x < n ==> |arr[x]| % 2 == 0
            decreases j
        {
            arr[j + 1] := arr[j];
            j := j - 1;
        }
        arr[j + 1] := key;
    }

    sorted := arr[0..n];
    assert |sorted| == |list|;
    assert IsPermutation(sorted, list);
    assert IsSortedByLength(sorted);
    assert forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0;
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
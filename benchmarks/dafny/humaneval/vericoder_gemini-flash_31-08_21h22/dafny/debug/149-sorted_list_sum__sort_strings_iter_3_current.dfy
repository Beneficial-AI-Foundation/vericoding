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
function CompareStrings(a: string, b: string): bool
    ensures (a == b) == (CompareStrings(a, b) == CompareStrings(b, a))
{
    comparison(a, b, 0)
}
// </vc-helpers>

// <vc-spec>
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
// </vc-spec>
// <vc-code>
{
    var n := |list|;
    if n == 0 {
        return [];
    }

    // Convert seq<string> to array<string> for in-place sorting
    var arr := new string[n];
    for i := 0 to n - 1 {
        arr[i] := list[i];
    }

    // Bubble sort algorithm using CompareStrings
    for i := n - 1 downto 1
        invariant 0 <= i < n
        invariant multiset(arr[0..n]) == multiset(list)
        invariant forall k, l :: i <= k < l < n ==> CompareStrings(arr[k], arr[l]) // items arr[i..n-1] are sorted among themselves
        invariant forall k :: 0 <= k < i ==> (forall l :: i <= l < n ==> CompareStrings(arr[k], arr[l])) // items arr[i..n-1] are greater than or equal to items arr[0..i-1]
    {
        for j := 0 to i - 1
            invariant 0 <= j < i
            invariant multiset(arr[0..n]) == multiset(list)
            invariant forall k, l :: i <= k < l < n ==> CompareStrings(arr[k], arr[l]) // items arr[i..n-1] are sorted among themselves
            invariant forall k :: 0 <= k <= j ==> (forall l :: i <= l < n ==> CompareStrings(arr[k], arr[l]))
            invariant forall k, l :: j < k < l < i ==> CompareStrings(arr[k], arr[l]) // items arr[j+1..i-1] are sorted among themselves
            invariant forall k :: 0 <= k < j ==> CompareStrings(arr[k], arr[j]) // arr[0..j-1] are sorted up to arr[j]
        {
            if !CompareStrings(arr[j], arr[j+1])
            {
                var temp := arr[j];
                arr[j] := arr[j+1];
                arr[j+1] := temp;
            }
        }
    }

    // Convert back to seq<string>
    sorted := arr[..];
    return sorted;
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
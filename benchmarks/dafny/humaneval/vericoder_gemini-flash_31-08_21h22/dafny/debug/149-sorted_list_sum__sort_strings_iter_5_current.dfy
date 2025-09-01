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
    ensures (a == b) == (a == b)
{
    comparison(a, b, 0)
}

function InvariantSortedPortion<T>(arr: array<T>, i: int, n: int, cmp: (T, T) -> bool): bool
{
    forall k, l :: i <= k < l < n ==> cmp(arr[k], arr[l])
}

function InvariantMinElements<T>(arr: array<T>, i: int, n: int, cmp: (T, T) -> bool): bool
{
    forall k :: 0 <= k <= i ==> (forall l :: i < l < n ==> cmp(arr[k], arr[l]))
}

// Function to check if elements in arr[0..j-1] are sorted relative to arr[j] by cmp
function InvariantPrefixSort<T>(arr: array<T>, j: int, cmp: (T, T) -> bool): bool
{
    forall k :: 0 <= k < j ==> cmp(arr[k], arr[j])
}
// </vc-helpers>

// <vc-spec>
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
// </vc-spec>
// <vc-code>
{
    var n := |list>;
    if n == 0 {
        return [];
    }

    // Convert seq<string> to array<string> for in-place sorting
    var arr := new string[n];
    for i := 0 to n - 1 {
        arr[i] := list[i];
    }

    // Bubble sort algorithm using CompareStrings
    for i := n - 1 downto 0
        invariant -1 <= i < n
        invariant multiset(arr[0..n]) == multiset(list)
        invariant InvariantSortedPortion(arr, i + 1, n, CompareStrings) // items arr[i+1..n-1] are sorted among themselves
        invariant InvariantMinElements(arr, i, n, CompareStrings) // items arr[i+1..n-1] are greater than or equal to items arr[0..i]
    {
        for j := 0 to i - 1
            invariant 0 <= j <= i
            invariant multiset(arr[0..n]) == multiset(list)
            invariant InvariantSortedPortion(arr, i + 1, n, CompareStrings) // items arr[i+1..n-1] are sorted among themselves
            invariant InvariantMinElements(arr, j, n, CompareStrings) // items arr[j+1..n-1] are greater than or equal to arr[0..j]
            invariant InvariantPrefixSort(arr, j, CompareStrings) // arr[0..j-1] are sorted up to arr[j]
            invariant forall k, l :: j < k < l <= i ==> CompareStrings(arr[k], arr[l]) // items arr[j+1..i] are sorted among themselves (before j+1 is swapped)
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
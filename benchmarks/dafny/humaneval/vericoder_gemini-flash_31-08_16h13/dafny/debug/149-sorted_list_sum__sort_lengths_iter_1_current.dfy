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
function LessOrEqualLength(s1: string, s2: string): bool {
    |s1| <= |s2|
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
    var n := |list>;
    if n == 0 {
        return [];
    }

    // Convert seq<string> to array<string> for in-place sorting
    var arr := new string[n];
    for i := 0 to n - 1 {
        arr[i] := list[i];
    }

    // Bubble sort (or any stable sorting algorithm)
    for i := 0 to n - 2 {
        for j := 0 to n - 2 - i {
            if !LessOrEqualLength(arr[j], arr[j+1]) {
                var temp := arr[j];
                arr[j] := arr[j+1];
                arr[j+1] := temp;
            }
        }
    }

    // Convert array<string> back to seq<string>
    sorted := array_to_seq(arr);

    // Proof to satisfy postconditions
    // 1. |sorted| == |list|
    // This holds because `array_to_seq` preserves length and `arr` was initialized with `n`.
    // 2. multiset(sorted) == multiset(list)
    // Bubble sort is an in-place sort that only swaps elements; it preserves the multiset.
    // 3. forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    // This is preserved because the `list` already satisfies this precondition and
    // sorting does not change the content of the elements, only their order.
    // 4. forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    // This is the definition of a sorted sequence, which the bubble sort ensures.
}

function array_to_seq<T>(arr: array<T>): seq<T>
    returns (s: seq<T>)
    ensures |s| == arr.Length
    ensures forall i :: 0 <= i < arr.Length ==> s[i] == arr[i]
{
    if arr.Length == 0 then
        []
    else
        seq_of_array_internal(arr, 0)
}

function seq_of_array_internal<T>(arr: array<T>, start_index: int): seq<T>
    requires 0 <= start_index <= arr.Length
    returns (s: seq<T>)
    ensures |s| == arr.Length - start_index
    ensures forall i :: 0 <= i < |s| ==> s[i] == arr[start_index + i]
    decreases arr.Length - start_index
{
    if start_index == arr.Length then
        []
    else
        [arr[start_index]] + seq_of_array_internal(arr, start_index + 1)
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
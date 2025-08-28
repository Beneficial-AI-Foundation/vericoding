// <vc-helpers>
lemma SortedArrayPreservation(arr: array<int>, target: int, index: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires arr != null
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.Length ==> arr[index] == target
    ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
// </vc-spec>
// </vc-spec>

// <vc-code>
method FindFirstOccurrenceImpl(arr: array<int>, target: int) returns (index: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.Length ==> arr[index] == target
    ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
    index := -1;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant index == -1 ==> forall k :: 0 <= k < i ==> arr[k] != target
        invariant 0 <= index < arr.Length ==> arr[index] == target && forall k :: 0 <= k < index ==> arr[k] != target
        invariant forall k :: 0 <= k < arr.Length ==> arr[k] == old(arr[k])
    {
        if arr[i] == target {
            index := i;
            return;
        }
        i := i + 1;
    }
    return;
}
// </vc-code>

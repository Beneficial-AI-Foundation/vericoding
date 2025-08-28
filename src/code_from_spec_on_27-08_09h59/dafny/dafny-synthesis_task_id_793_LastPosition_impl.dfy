// <vc-helpers>
lemma BinarySearchInvariant(arr: array<int>, elem: int, left: int, right: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    requires 0 <= left <= right <= arr.Length
    requires forall i :: 0 <= i < left ==> arr[i] < elem
    requires forall i :: right <= i < arr.Length ==> arr[i] > elem
    ensures forall i :: 0 <= i < arr.Length && arr[i] == elem ==> left <= i < right

lemma LastOccurrenceProperty(arr: array<int>, elem: int, pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    requires 0 <= pos < arr.Length
    requires arr[pos] == elem
    requires pos == arr.Length - 1 || arr[pos + 1] > elem
    ensures forall i :: pos < i < arr.Length ==> arr[i] != elem
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos <= arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var left := 0;
    var right := arr.Length;
    
    while left < right
        invariant 0 <= left <= right <= arr.Length
        invariant forall i :: 0 <= i < left ==> arr[i] <= elem
        invariant forall i :: right <= i < arr.Length ==> arr[i] > elem
    {
        var mid := left + (right - left) / 2;
        
        if arr[mid] <= elem {
            left := mid + 1;
        } else {
            right := mid;
        }
    }
    
    if left > 0 && arr[left - 1] == elem {
        pos := left - 1;
    } else {
        pos := -1;
    }
}
// </vc-code>

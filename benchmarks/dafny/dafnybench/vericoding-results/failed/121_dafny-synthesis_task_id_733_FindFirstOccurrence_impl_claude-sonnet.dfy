

// <vc-helpers>
lemma BinarySearchCorrectness(arr: array<int>, target: int, left: int, right: int, mid: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    requires 0 <= left <= right <= arr.Length
    requires left <= mid < right
    requires arr[mid] >= target
    ensures forall i :: left <= i < mid ==> arr[i] < target
{
    if mid > left {
        assert forall i :: left <= i < mid ==> arr[i] <= arr[mid-1];
        assert arr[mid-1] <= arr[mid];
        if arr[mid-1] >= target {
            assert arr[mid-1] >= target && arr[mid] >= target;
            assert arr[mid-1] <= arr[mid];
        }
    }
}

lemma SortedArrayProperty(arr: array<int>, i: int, j: int)
    requires forall x, y :: 0 <= x < y < arr.Length ==> arr[x] <= arr[y]
    requires 0 <= i <= j < arr.Length
    ensures arr[i] <= arr[j]
{
}
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires arr != null
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.Length ==> arr[index] == target
    ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
// </vc-spec>
// <vc-code>
{
    if arr.Length == 0 {
        return -1;
    }
    
    var left := 0;
    var right := arr.Length;
    
    while left < right
        invariant 0 <= left <= right <= arr.Length
        invariant forall i :: 0 <= i < left ==> arr[i] < target
        invariant forall i :: right <= i < arr.Length ==> arr[i] >= target
        invariant forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
    {
        var mid := left + (right - left) / 2;
        
        if arr[mid] < target {
            left := mid + 1;
        } else {
            right := mid;
        }
    }
    
    if left < arr.Length && arr[left] == target {
        return left;
    } else {
        return -1;
    }
}
// </vc-code>


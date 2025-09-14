

// <vc-helpers>
predicate sorted(arr: array<int>)
    reads arr
{
    forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
}

lemma SortedSubarray(arr: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= arr.Length
    requires sorted(arr)
    ensures forall i, j :: lo <= i < j < hi ==> arr[i] <= arr[j]
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
    var result := -1;
    
    while left < right
        invariant 0 <= left <= right <= arr.Length
        invariant result == -1 || (0 <= result < arr.Length && arr[result] == target)
        invariant forall i :: 0 <= i < left ==> arr[i] < target
        invariant forall i :: right <= i < arr.Length ==> arr[i] > target || (arr[i] == target && result != -1 && result <= i)
        invariant result != -1 ==> left <= result <= right
        invariant result != -1 ==> forall i :: 0 <= i < left ==> arr[i] != target
    {
        var mid := left + (right - left) / 2;
        
        if arr[mid] == target {
            result := mid;
            right := mid;
        } else if arr[mid] < target {
            left := mid + 1;
        } else {
            right := mid;
        }
    }
    
    if result == -1 {
        assert left == right;
        assert forall i :: 0 <= i < left ==> arr[i] < target;
        assert forall i :: right <= i < arr.Length ==> arr[i] > target;
        assert forall i :: 0 <= i < arr.Length ==> arr[i] != target;
    }
    
    index := result;
}
// </vc-code>


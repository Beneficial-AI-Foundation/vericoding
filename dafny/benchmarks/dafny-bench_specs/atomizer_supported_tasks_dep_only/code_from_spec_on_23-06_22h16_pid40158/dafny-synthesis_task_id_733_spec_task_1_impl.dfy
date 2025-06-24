//IMPL 
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires arr != null
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.Length ==> arr[index] == target
    ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
    if arr.Length == 0 {
        return -1;
    }
    
    var left := 0;
    var right := arr.Length - 1;
    index := -1;
    
    /* code modified by LLM (iteration 4): Strengthened loop invariants to ensure complete logical coverage */
    while left <= right
        invariant 0 <= left <= arr.Length
        invariant -1 <= right < arr.Length
        invariant index == -1 || (0 <= index < arr.Length && arr[index] == target)
        invariant forall i :: 0 <= i < left ==> arr[i] < target
        invariant forall i :: right < i < arr.Length ==> arr[i] > target
        invariant forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
        invariant index != -1 ==> (forall i :: 0 <= i < index ==> arr[i] < target)
        invariant index != -1 ==> (left <= index)
        invariant (forall i :: 0 <= i < left ==> arr[i] < target) && (forall i :: right < i < arr.Length ==> arr[i] > target) && left > right ==> (forall i :: 0 <= i < arr.Length ==> arr[i] != target)
    {
        var mid := left + (right - left) / 2;
        
        if arr[mid] == target {
            index := mid;
            /* code modified by LLM (iteration 4): Added assertion to maintain invariant about elements before index */
            assert forall i :: 0 <= i < left ==> arr[i] < target;
            assert left <= mid;
            right := mid - 1;  // Continue searching left for first occurrence
        } else if arr[mid] < target {
            left := mid + 1;
        } else {
            assert arr[mid] > target;
            right := mid - 1;
        }
    }
    
    /* code modified by LLM (iteration 4): Enhanced postcondition proof with explicit reasoning */
    if index != -1 {
        assert arr[index] == target;
        assert forall i :: 0 <= i < index ==> arr[i] < target;
    } else {
        assert left > right;
        assert forall i :: 0 <= i < left ==> arr[i] < target;
        assert forall i :: right < i < arr.Length ==> arr[i] > target;
        /* code modified by LLM (iteration 4): Added helper assertion to bridge the gap in reasoning */
        assert left == right + 1;
        assert forall i :: 0 <= i <= right ==> arr[i] < target;
        assert forall i :: left <= i < arr.Length ==> arr[i] > target;
        assert forall i :: 0 <= i < arr.Length ==> (i <= right || i >= left);
        assert forall i :: 0 <= i < arr.Length ==> arr[i] != target;
    }
}
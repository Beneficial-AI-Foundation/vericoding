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
    
    while left <= right
        invariant 0 <= left <= arr.Length
        invariant -1 <= right < arr.Length
        invariant left <= right + 1
        /* code modified by LLM (iteration 4): invariant for elements before left */
        invariant forall i :: 0 <= i < left ==> arr[i] < target
        /* code modified by LLM (iteration 4): invariant for elements after right */
        invariant forall i :: right < i < arr.Length ==> arr[i] > target
        /* code modified by LLM (iteration 4): invariant for found index validity */
        invariant index == -1 || (0 <= index < arr.Length && arr[index] == target)
        /* code modified by LLM (iteration 4): invariant ensuring index is leftmost occurrence found so far */
        invariant index != -1 ==> forall i :: 0 <= i < index ==> arr[i] < target
        /* code modified by LLM (iteration 4): invariant ensuring index is in valid range relative to search */
        invariant index != -1 ==> index >= left
        /* code modified by LLM (iteration 4): array immutability invariant */
        invariant forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
        decreases right - left + 1
    {
        var mid := left + (right - left) / 2;
        
        if arr[mid] == target {
            index := mid;
            /* code modified by LLM (iteration 4): continue searching left to find first occurrence */
            right := mid - 1;
        } else if arr[mid] < target {
            left := mid + 1;
        } else {
            right := mid - 1;
        }
    }
    
    /* code modified by LLM (iteration 4): final verification assertions */
    if index == -1 {
        /* code modified by LLM (iteration 4): prove no target exists using loop invariants */
        assert left > right;
        assert forall i :: 0 <= i < left ==> arr[i] < target;
        assert forall i :: right < i < arr.Length ==> arr[i] > target;
        /* code modified by LLM (iteration 4): show all indices are covered */
        forall i | 0 <= i < arr.Length
            ensures arr[i] != target
        {
            if i < left {
                assert arr[i] < target;
            } else {
                assert i > right;
                assert arr[i] > target;
            }
        }
    } else {
        /* code modified by LLM (iteration 4): prove index is valid and points to target */
        assert 0 <= index < arr.Length;
        assert arr[index] == target;
        /* code modified by LLM (iteration 4): prove this is the first occurrence */
        assert forall i :: 0 <= i < index ==> arr[i] < target;
    }
}
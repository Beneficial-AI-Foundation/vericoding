//IMPL FindFirstOccurrence
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
        /* code modified by LLM (iteration 4): ensure index validity and target match */
        invariant index == -1 || (0 <= index < arr.Length && arr[index] == target)
        /* code modified by LLM (iteration 4): if index found, it's the first occurrence in searched area */
        invariant index != -1 ==> forall i :: 0 <= i < index ==> arr[i] != target
        /* code modified by LLM (iteration 4): no target found in eliminated left region */
        invariant forall i :: 0 <= i < left ==> arr[i] != target
        /* code modified by LLM (iteration 4): no target found in eliminated right region */
        invariant forall i :: right < i < arr.Length ==> arr[i] != target
        /* code modified by LLM (iteration 4): if we found an index, it's in the remaining search space */
        invariant index != -1 ==> left <= index <= right + 1
    {
        var mid := left + (right - left) / 2;
        
        if arr[mid] == target {
            index := mid;
            /* code modified by LLM (iteration 4): search left half to find first occurrence */
            right := mid - 1;
        } else if arr[mid] < target {
            left := mid + 1;
        } else {
            right := mid - 1;
        }
    }
    
    /* code modified by LLM (iteration 4): final verification using loop invariants */
    if index != -1 {
        assert arr[index] == target;
        assert forall i :: 0 <= i < index ==> arr[i] != target;
    } else {
        /* code modified by LLM (iteration 4): prove no target exists using eliminated regions */
        assert left > right;
        assert forall i :: 0 <= i < left ==> arr[i] != target;
        assert forall i :: right < i < arr.Length ==> arr[i] != target;
        /* code modified by LLM (iteration 4): use the fact that left > right means we've covered everything */
        assert left == right + 1;
        forall i | 0 <= i < arr.Length
            ensures arr[i] != target
        {
            if i < left {
                assert arr[i] != target; // from left invariant
            } else {
                assert i > right; // since i >= left and left > right
                assert arr[i] != target; // from right invariant
            }
        }
    }
}
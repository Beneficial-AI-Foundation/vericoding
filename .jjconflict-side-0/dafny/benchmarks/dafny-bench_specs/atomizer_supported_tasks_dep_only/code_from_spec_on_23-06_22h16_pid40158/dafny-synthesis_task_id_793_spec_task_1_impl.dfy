//IMPL 
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos <= arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
    var left := 0;
    var right := arr.Length - 1;
    pos := -1;
    
    while left <= right
        invariant 0 <= left <= arr.Length
        invariant -1 <= right < arr.Length
        invariant pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem)
        invariant forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
        /* code modified by LLM (iteration 1): Fixed invariants to properly track search bounds and rightmost position */
        invariant forall i :: 0 <= i < left ==> arr[i] <= elem
        invariant forall i :: right < i < arr.Length ==> arr[i] > elem
        invariant pos == -1 ==> forall i :: 0 <= i < left ==> arr[i] != elem
        invariant pos != -1 ==> (pos < left && arr[pos] == elem && forall i :: pos < i < left ==> arr[i] != elem)
    {
        var mid := left + (right - left) / 2;
        
        if arr[mid] == elem {
            pos := mid;
            left := mid + 1;
        } else if arr[mid] < elem {
            left := mid + 1;
        } else {
            right := mid - 1;
        }
    }
    
    /* code modified by LLM (iteration 1): Added comprehensive assertions to establish postcondition */
    if pos != -1 {
        assert arr[pos] == elem;
        assert pos < arr.Length;
        
        // Establish that pos is the rightmost occurrence
        assert forall i :: pos < i < left ==> arr[i] != elem;
        assert left <= arr.Length;
        assert forall i :: right < i < arr.Length ==> arr[i] > elem;
        assert left > right;
        
        // Since right < left and we've established bounds, we know about elements after pos
        if pos < arr.Length - 1 {
            assert pos + 1 < arr.Length;
            if pos + 1 < left {
                assert arr[pos + 1] != elem;
                assert forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j];
                assert arr[pos] <= arr[pos + 1];
                assert arr[pos] == elem;
                assert arr[pos + 1] != elem;
                assert arr[pos + 1] > elem;
            } else {
                assert pos + 1 >= left;
                assert pos + 1 > right;
                assert arr[pos + 1] > elem;
            }
        }
    }
}
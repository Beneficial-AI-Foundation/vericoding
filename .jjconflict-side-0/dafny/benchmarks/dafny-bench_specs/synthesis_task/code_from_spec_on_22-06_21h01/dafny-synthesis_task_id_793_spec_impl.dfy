//IMPL LastPosition
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos == arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
    var left := 0;
    var right := arr.Length - 1;
    pos := -1;
    
    /* code modified by LLM (iteration 2): corrected loop invariants to properly track rightmost occurrence */
    while left <= right
        invariant 0 <= left <= arr.Length
        invariant -1 <= right < arr.Length
        invariant pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem)
        invariant forall i :: 0 <= i < left ==> arr[i] <= elem
        invariant forall i :: right < i < arr.Length ==> arr[i] > elem
        invariant pos == -1 || (0 <= pos < left)
        invariant pos != -1 ==> forall i :: pos < i < left ==> arr[i] > elem
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
    
    /* code modified by LLM (iteration 2): fixed postcondition establishment using correct invariants */
    if pos != -1 {
        assert arr[pos] == elem;
        assert 0 <= pos < arr.Length;
        
        // Prove that pos is the last occurrence
        if pos < arr.Length - 1 {
            // From loop invariants when loop terminates (left > right):
            // - pos < left (since pos was found before left was incremented past it)
            // - forall i :: pos < i < left ==> arr[i] > elem
            // - forall i :: right < i < arr.Length ==> arr[i] > elem
            // Since left > right, we have pos < left and pos + 1 >= left or pos + 1 <= right
            
            assert forall i :: pos < i < left ==> arr[i] > elem;
            assert forall i :: right < i < arr.Length ==> arr[i] > elem;
            
            if pos + 1 < left {
                assert arr[pos + 1] > elem;
            } else {
                // pos + 1 >= left, and since left > right, we have pos + 1 > right
                assert pos + 1 > right;
                assert arr[pos + 1] > elem;
            }
        }
    }
}
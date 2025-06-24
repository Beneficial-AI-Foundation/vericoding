//IMPL 
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos <= arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
    pos := -1;
    var i := 0;
    
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant pos == -1 || (0 <= pos < i && arr[pos] == elem)
        invariant forall k :: 0 <= k < i && arr[k] == elem ==> k <= pos
    {
        if arr[i] == elem {
            pos := i;
        }
        i := i + 1;
    }
    
    if pos != -1 {
        assert arr[pos] == elem;
        assert pos < arr.Length;
        if pos < arr.Length - 1 {
            assert forall k :: pos < k < arr.Length ==> arr[k] >= arr[pos];
            assert forall k :: pos < k < arr.Length && arr[k] == elem ==> false;
            assert arr[pos + 1] > elem;
        }
    }
}
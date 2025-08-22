//IMPL 
method MoveZeroesToEnd(arr: array<int>)
    requires arr.Length >= 2
    modifies arr
    // Same size
    ensures arr.Length == old(arr.Length)
    // Zeros to the right of the first zero
    ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
    // The final array is a permutation of the original one
    ensures multiset(arr[..]) == multiset(old(arr[..]))
    // Relative order of non-zero elements is preserved
    ensures forall n, m /* on old array */:: 0 <= n < m < arr.Length && old(arr[n]) != 0 && old(arr[m]) != 0 ==> 
            exists k, l /* on new array */:: 0 <= k < l < arr.Length && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
    //ensures IsOrderPreserved(arr[..], old(arr[..]))
    // Number of zeros is preserved
{
    /* code modified by LLM (iteration 1): Added ghost variable to track original array state */
    ghost var originalArr := arr[..];
    var writePos := 0;
    var readPos := 0;
    
    while readPos < arr.Length
        invariant 0 <= writePos <= readPos <= arr.Length
        invariant forall i :: 0 <= i < writePos ==> arr[i] != 0
        invariant multiset(arr[..]) == multiset(originalArr)
        /* code modified by LLM (iteration 1): Strengthened invariant for order preservation */
        invariant forall n, m :: 0 <= n < m < readPos && originalArr[n] != 0 && originalArr[m] != 0 ==>
                 (originalArr[n] in arr[..writePos] && originalArr[m] in arr[..writePos] ==>
                  exists k, l :: 0 <= k < l < writePos && arr[k] == originalArr[n] && arr[l] == originalArr[m])
        /* code modified by LLM (iteration 1): Added invariant to track processed non-zero elements */
        invariant forall i :: 0 <= i < readPos && originalArr[i] != 0 ==> originalArr[i] in arr[..writePos]
        /* code modified by LLM (iteration 1): Added invariant for unprocessed elements */
        invariant forall i :: readPos <= i < arr.Length ==> arr[i] == originalArr[i]
    {
        if arr[readPos] != 0 {
            if readPos != writePos {
                /* code modified by LLM (iteration 1): Added assertion to help verification */
                assert arr[readPos] == originalArr[readPos];
                arr[writePos] := arr[readPos];
                arr[readPos] := 0;
            }
            writePos := writePos + 1;
        }
        readPos := readPos + 1;
    }
    
    /* code modified by LLM (iteration 1): Added post-loop assertions to help prove postconditions */
    assert multiset(arr[..]) == multiset(originalArr);
    assert forall i :: 0 <= i < writePos ==> arr[i] != 0;
    assert forall i :: writePos <= i < arr.Length ==> arr[i] == 0;
}

//IMPL 
method swap(arr: array<int>, i: int, j: int)
    requires arr.Length > 0
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    modifies arr
    ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
    ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{
    /* code modified by LLM (iteration 1): Added case handling for when i == j */
    if i == j {
        return;
    }
    
    var temp := arr[i];
    arr[i] := arr[j];
    arr[j] := temp;
}

//ATOM 
function count(arr: seq<int>, value: int) : (c: nat)
    ensures c <= |arr|
{
    if |arr| == 0 then 0 else (if arr[0] == value then 1 else 0) + count(arr[1..], value)
}
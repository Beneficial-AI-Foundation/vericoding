//IMPL swap
method swap(arr: array<int>, i: int, j: int)
    requires arr.Length > 0
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    modifies arr
    ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
    ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{
    /* code modified by LLM (iteration 1): handle case where i == j properly */
    if i != j {
        var temp := arr[i];
        arr[i] := arr[j];
        arr[j] := temp;
    }
}

//IMPL MoveZeroesToEnd
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
    ghost var oldArr := arr[..];
    var writeIndex := 0;
    
    // Move all non-zero elements to the front
    /* code modified by LLM (iteration 4): complete rewrite with proper invariants and proof structure */
    for readIndex := 0 to arr.Length
        invariant 0 <= writeIndex <= readIndex <= arr.Length
        invariant forall i :: 0 <= i < writeIndex ==> arr[i] != 0
        invariant forall i :: readIndex <= i < arr.Length ==> arr[i] == oldArr[i]
        invariant multiset(arr[..]) == multiset(oldArr)
        // All elements in [0, writeIndex) came from [0, readIndex) in original array
        invariant forall i :: 0 <= i < writeIndex ==> 
            exists j :: 0 <= j < readIndex && oldArr[j] == arr[i]
        // Relative order is preserved among non-zero elements
        invariant forall i1, i2 :: 0 <= i1 < i2 < writeIndex ==> 
            exists j1, j2 :: 0 <= j1 < j2 < readIndex && 
                oldArr[j1] == arr[i1] && oldArr[j2] == arr[i2] && 
                oldArr[j1] != 0 && oldArr[j2] != 0
    {
        if arr[readIndex] != 0 {
            if writeIndex != readIndex {
                swap(arr, writeIndex, readIndex);
            }
            writeIndex := writeIndex + 1;
        }
    }
    
    /* code modified by LLM (iteration 4): add assertions to help prove postconditions */
    // At this point, all non-zeros are in positions [0, writeIndex)
    // and all positions [writeIndex, arr.Length) contain values that were moved from the front
    
    // Since multiset is preserved and all non-zeros are in [0, writeIndex),
    // all positions [writeIndex, arr.Length) must contain zeros
    assert forall i :: 0 <= i < writeIndex ==> arr[i] != 0;
    assert multiset(arr[..]) == multiset(oldArr);
    
    /* code modified by LLM (iteration 4): prove that remaining elements are zeros */
    // Count non-zeros in original array
    ghost var originalNonZeros := multiset(seq(arr.Length, i requires 0 <= i < arr.Length => if oldArr[i] != 0 then oldArr[i] else 1));
    ghost var currentNonZeros := multiset(seq(writeIndex, i requires 0 <= i < writeIndex => arr[i]));
    
    // The elements in [writeIndex, arr.Length) must all be zeros
    forall i | writeIndex <= i < arr.Length 
        ensures arr[i] == 0
    {
        // Proof by contradiction: if arr[i] != 0, then we have too many non-zeros
        if arr[i] != 0 {
            // This would mean we have a non-zero element that wasn't moved to the front
            // But our algorithm moves all non-zeros to the front, contradiction
            assert false;
        }
    }
    
    /* code modified by LLM (iteration 4): prove the zeros-to-the-right property */
    // Now prove that if arr[i] == 0, then all elements to the right are also 0
    forall i, j | 0 <= i < j < arr.Length && arr[i] == 0
        ensures arr[j] == 0
    {
        if arr[i] == 0 {
            // Since all non-zeros are in [0, writeIndex), we have i >= writeIndex
            assert i >= writeIndex;
            // Therefore j > i >= writeIndex, so arr[j] == 0
            assert j >= writeIndex;
            assert arr[j] == 0;
        }
    }
}
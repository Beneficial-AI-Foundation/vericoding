//IMPL FindEvenNumbers
method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
 ensures forall x :: x in evenNumbers[..] ==> x in arr[..]
 ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
 ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
 ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
              exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
    // First pass: count even numbers
    var evenCount := 0;
    var i := 0;
    /* code modified by LLM (iteration 4): fixed set comprehension syntax */
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant evenCount >= 0
        invariant evenCount == |set k | 0 <= k < i && arr[k] % 2 == 0 :: k|
    {
        if arr[i] % 2 == 0 {
            evenCount := evenCount + 1;
        }
        i := i + 1;
    }
    
    // Create result array
    evenNumbers := new int[evenCount];
    
    // Second pass: fill the result array
    var j := 0;
    i := 0;
    /* code modified by LLM (iteration 4): added ghost variable to track source indices */
    ghost var sourceIndices: seq<int> := [];
    
    /* code modified by LLM (iteration 4): corrected invariants with proper set syntax */
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant 0 <= j <= evenNumbers.Length
        invariant j == |set k | 0 <= k < i && arr[k] % 2 == 0 :: k|
        invariant forall k :: 0 <= k < j ==> evenNumbers[k] % 2 == 0
        invariant forall k :: 0 <= k < j ==> evenNumbers[k] in arr[..]
        invariant forall k :: 0 <= k < j ==> exists n :: 0 <= n < i && evenNumbers[k] == arr[n]
        invariant |sourceIndices| == j
        invariant forall k :: 0 <= k < j ==> 0 <= sourceIndices[k] < i && evenNumbers[k] == arr[sourceIndices[k]]
        invariant forall k1, k2 :: 0 <= k1 < k2 < j ==> sourceIndices[k1] < sourceIndices[k2]
        invariant forall x :: x in evenNumbers[0..j] ==> x in arr[0..i]
        invariant forall x :: x !in arr[0..i] ==> x !in evenNumbers[0..j]
    {
        if arr[i] % 2 == 0 {
            evenNumbers[j] := arr[i];
            /* code modified by LLM (iteration 4): update ghost variable with current index */
            sourceIndices := sourceIndices + [i];
            j := j + 1;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): added helper assertions to establish postconditions */
    assert i == arr.Length;
    assert j == evenCount;
    assert j == evenNumbers.Length;
    assert evenNumbers[..] == evenNumbers[0..j];
    assert arr[..] == arr[0..i];
    
    /* code modified by LLM (iteration 4): prove the ordering property using sourceIndices */
    assert forall k1, k2 :: 0 <= k1 < k2 < evenNumbers.Length ==> 
        0 <= sourceIndices[k1] < sourceIndices[k2] < arr.Length &&
        evenNumbers[k1] == arr[sourceIndices[k1]] && 
        evenNumbers[k2] == arr[sourceIndices[k2]];
}
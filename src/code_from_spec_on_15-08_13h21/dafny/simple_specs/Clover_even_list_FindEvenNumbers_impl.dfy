method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
 ensures forall x :: x in evenNumbers[..] ==> x in arr[..]
 ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
 ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
 ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
              exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
    var count := 0;
    var i := 0;
    
    // First pass: count even numbers
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        /* code modified by LLM (iteration 4): simplified invariant to count even numbers found so far */
        invariant count == |set k | 0 <= k < i && arr[k] % 2 == 0|
    {
        if arr[i] % 2 == 0 {
            count := count + 1;
            /* code modified by LLM (iteration 4): fixed assertion syntax for set operations */
            assert arr[i] % 2 == 0;
            assert i in set k | 0 <= k < i + 1 && arr[k] % 2 == 0;
            assert (set k | 0 <= k < i + 1 && arr[k] % 2 == 0) == 
                   (set k | 0 <= k < i && arr[k] % 2 == 0) + {i};
        }
        i := i + 1;
    }
    
    // Create result array
    evenNumbers := new int[count];
    
    if count == 0 {
        return;
    }
    
    // Second pass: fill the result array
    /* code modified by LLM (iteration 4): added array to track original positions */
    var positions := new int[count];
    i := 0;
    var j := 0;
    
    while i < arr.Length && j < count
        invariant 0 <= i <= arr.Length
        invariant 0 <= j <= count
        /* code modified by LLM (iteration 4): replaced set cardinality with simpler counting invariant */
        invariant j <= |set k | 0 <= k < i && arr[k] % 2 == 0|
        invariant forall k :: 0 <= k < j ==> evenNumbers[k] % 2 == 0
        invariant forall k :: 0 <= k < j ==> evenNumbers[k] in arr[..]
        invariant forall k :: 0 <= k < j ==> 0 <= positions[k] < i && evenNumbers[k] == arr[positions[k]]
        invariant forall k1, k2 :: 0 <= k1 < k2 < j ==> positions[k1] < positions[k2]
        /* code modified by LLM (iteration 4): added invariant to ensure we collect all even numbers */
        invariant forall k :: 0 <= k < i && arr[k] % 2 == 0 ==> 
            (exists idx :: 0 <= idx < j && evenNumbers[idx] == arr[k] && positions[idx] == k)
    {
        if arr[i] % 2 == 0 {
            evenNumbers[j] := arr[i];
            positions[j] := i;
            j := j + 1;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): strengthened assertions to help prove postconditions */
    assert i == arr.Length;
    assert j == |set k | 0 <= k < arr.Length && arr[k] % 2 == 0|;
    assert j == count;
    assert forall k :: 0 <= k < j ==> evenNumbers[k] % 2 == 0;
    assert forall k :: 0 <= k < j ==> evenNumbers[k] in arr[..];
    assert forall k1, k2 :: 0 <= k1 < k2 < j ==> positions[k1] < positions[k2];
    assert forall k1, k2 :: 0 <= k1 < k2 < evenNumbers.Length ==>
        exists n1, n2 :: 0 <= n1 < n2 < arr.Length && evenNumbers[k1] == arr[n1] && evenNumbers[k2] == arr[n2];
}
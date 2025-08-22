// IMPL
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
    /* code modified by LLM (iteration 4): Store original array for postcondition verification */
    var originalArr := arr[..];
    var writeIndex := 0;
    
    /* code modified by LLM (iteration 4): Track non-zero elements in order for relative order preservation */
    var nonZeroElements: seq<int> := [];
    
    /* code modified by LLM (iteration 4): First pass with proper loop syntax and comprehensive invariants */
    // First pass: move all non-zero elements to the front
    var readIndex := 0;
    while readIndex < arr.Length
        invariant 0 <= writeIndex <= readIndex <= arr.Length
        invariant forall i :: 0 <= i < writeIndex ==> arr[i] != 0
        invariant |nonZeroElements| == writeIndex
        invariant forall i :: 0 <= i < writeIndex ==> arr[i] == nonZeroElements[i]
        invariant forall i :: 0 <= i < |nonZeroElements| ==> nonZeroElements[i] in multiset(originalArr)
        invariant multiset(arr[..writeIndex]) + multiset(arr[readIndex..]) == multiset(originalArr)
        invariant forall i, j :: 0 <= i < j < |nonZeroElements| ==> 
            exists n, m :: 0 <= n < m < |originalArr| && originalArr[n] == nonZeroElements[i] && originalArr[m] == nonZeroElements[j]
    {
        if arr[readIndex] != 0 {
            arr[writeIndex] := arr[readIndex];
            nonZeroElements := nonZeroElements + [arr[readIndex]];
            writeIndex := writeIndex + 1;
        }
        readIndex := readIndex + 1;
    }
    
    /* code modified by LLM (iteration 4): Store writeIndex for zero-filling phase */
    var nonZeroCount := writeIndex;
    
    /* code modified by LLM (iteration 4): Second pass with proper loop syntax */
    // Second pass: fill remaining positions with zeros
    var i := writeIndex;
    while i < arr.Length
        invariant writeIndex <= i <= arr.Length
        invariant forall j :: 0 <= j < writeIndex ==> arr[j] != 0
        invariant forall j :: writeIndex <= j < i ==> arr[j] == 0
        invariant multiset(arr[..writeIndex]) + multiset(arr[writeIndex..i]) + multiset(arr[i..]) == multiset(originalArr)
    {
        arr[i] := 0;
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Prove multiset equality */
    assert multiset(arr[..]) == multiset(arr[..nonZeroCount]) + multiset(arr[nonZeroCount..]);
    assert multiset(arr[..nonZeroCount]) == multiset(nonZeroElements);
    assert forall j :: nonZeroCount <= j < arr.Length ==> arr[j] == 0;
    
    /* code modified by LLM (iteration 4): Prove zeros clustering property */
    if nonZeroCount < arr.Length {
        assert arr[nonZeroCount] == 0;
        forall i, j | 0 <= i < j < arr.Length && arr[i] == 0
            ensures arr[j] == 0
        {
            if i < nonZeroCount {
                assert arr[i] != 0;
                assert false;
            } else {
                assert i >= nonZeroCount;
                assert j > i >= nonZeroCount;
                assert arr[j] == 0;
            }
        }
    }
    
    /* code modified by LLM (iteration 4): Prove relative order preservation */
    forall n, m | 0 <= n < m < arr.Length && originalArr[n] != 0 && originalArr[m] != 0
        ensures exists k, l :: 0 <= k < l < arr.Length && arr[k] == originalArr[n] && arr[l] == originalArr[m]
    {
        assert originalArr[n] in nonZeroElements;
        assert originalArr[m] in nonZeroElements;
        var k := FindInSequence(nonZeroElements, originalArr[n]);
        var l := FindInSequence(nonZeroElements, originalArr[m]);
        assert 0 <= k < l < nonZeroCount <= arr.Length;
        assert arr[k] == originalArr[n] && arr[l] == originalArr[m];
    }
}

/* code modified by LLM (iteration 4): Helper function to find element in sequence */
function FindInSequence(s: seq<int>, x: int): nat
    requires x in s
    ensures FindInSequence(s, x) < |s|
    ensures s[FindInSequence(s, x)] == x
{
    if s[0] == x then 0 else 1 + FindInSequence(s[1..], x)
}

// IMPL
method swap(arr: array<int>, i: int, j: int)
    requires arr.Length > 0
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    modifies arr
    ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
    ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{
    /* code modified by LLM (iteration 4): Handle case where i == j */
    if i == j {
        return;
    }
    
    /* code modified by LLM (iteration 4): Standard swap implementation */
    var temp := arr[i];
    arr[i] := arr[j];
    arr[j] := temp;
}

// ATOM
function count(arr: seq<int>, value: int) : (c: nat)
    ensures c <= |arr|
{
    if |arr| == 0 then 0 else (if arr[0] == value then 1 else 0) + count(arr[1..], value)
}
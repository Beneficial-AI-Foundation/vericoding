method swap(arr: array<int>, i: int, j: int)
    requires arr.Length > 0
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    modifies arr
    ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
    ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{
  assume{:axiom} false;
}

function count(arr: seq<int>, value: int) : (c: nat)
    ensures c <= |arr|
{
    if |arr| == 0 then 0 else (if arr[0] == value then 1 else 0) + count(arr[1..], value)
}

// <vc-helpers>
lemma MultisetPreservedAfterSwap(arr: array<int>, i: int, j: int)
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    ensures multiset(arr[..][i := arr[j]][j := arr[i]]) == multiset(arr[..])
{
    var original := arr[..];
    var after_swap := original[i := arr[j]][j := arr[i]];
    
    if i == j {
        assert after_swap == original;
    } else {
        assert multiset(after_swap) == multiset(original);
    }
}

lemma ArraySlicePreservation(arr: array<int>, writeIndex: int, readIndex: int)
    requires 0 <= writeIndex <= readIndex < arr.Length
    requires forall k :: writeIndex <= k < readIndex ==> arr[k] != 0
    ensures forall k :: 0 <= k < writeIndex ==> arr[k] != 0
{
}

lemma ZeroClusterProperty(arr: array<int>)
    requires forall i :: 0 <= i < arr.Length && arr[i] == 0 ==> 
             forall j :: i < j < arr.Length ==> arr[j] == 0
    ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
{
}

lemma NonZeroOrderPreservation(oldArr: seq<int>, newArr: seq<int>, nonZeroPositions: seq<int>)
    requires |oldArr| == |newArr|
    requires forall i :: 0 <= i < |nonZeroPositions| ==> 
             0 <= nonZeroPositions[i] < |newArr| && newArr[nonZeroPositions[i]] != 0
    requires forall i :: 0 <= i < |nonZeroPositions| - 1 ==> nonZeroPositions[i] < nonZeroPositions[i+1]
    ensures forall n, m :: 0 <= n < m < |oldArr| && oldArr[n] != 0 && oldArr[m] != 0 ==>
            exists k, l :: 0 <= k < l < |newArr| && newArr[k] == oldArr[n] && newArr[l] == oldArr[m]
{
}

lemma OrderPreservationHelper(arr: array<int>, originalArray: seq<int>, writeIndex: int, readIndex: int)
    requires 0 <= writeIndex <= readIndex <= arr.Length
    requires |originalArray| == arr.Length
    requires forall n, m :: (0 <= n < m < readIndex && originalArray[n] != 0 && originalArray[m] != 0) ==>
             (exists k, l :: 0 <= k < l < writeIndex && arr[k] == originalArray[n] && arr[l] == originalArray[m])
    ensures forall n, m :: (0 <= n < m < arr.Length && originalArray[n] != 0 && originalArray[m] != 0) ==>
            (exists k, l :: 0 <= k < l < writeIndex && arr[k] == originalArray[n] && arr[l] == originalArray[m])
{
}

lemma OrderPreservationAfterLoop(arr: array<int>, originalArray: seq<int>, writeIndex: int)
    requires writeIndex <= arr.Length
    requires |originalArray| == arr.Length
    requires forall k :: 0 <= k < writeIndex ==> arr[k] != 0
    requires forall n, m :: (0 <= n < m < arr.Length && originalArray[n] != 0 && originalArray[m] != 0) ==>
             (exists k, l :: 0 <= k < l < writeIndex && arr[k] == originalArray[n] && arr[l] == originalArray[m])
    ensures forall n, m :: 0 <= n < m < arr.Length && originalArray[n] != 0 && originalArray[m] != 0 ==> 
            exists k, l :: 0 <= k < l < arr.Length && arr[k] == originalArray[n] && arr[l] == originalArray[m]
{
    forall n, m | 0 <= n < m < arr.Length && originalArray[n] != 0 && originalArray[m] != 0
    ensures exists k, l :: 0 <= k < l < arr.Length && arr[k] == originalArray[n] && arr[l] == originalArray[m]
    {
        assert exists k, l :: 0 <= k < l < writeIndex && arr[k] == originalArray[n] && arr[l] == originalArray[m];
        var k, l :| 0 <= k < l < writeIndex && arr[k] == originalArray[n] && arr[l] == originalArray[m];
        assert 0 <= k < l < arr.Length && arr[k] == originalArray[n] && arr[l] == originalArray[m];
    }
}

lemma ZeroClusterAfterSecondLoop(arr: array<int>, writeIndex: int)
    requires writeIndex <= arr.Length
    requires forall k :: 0 <= k < writeIndex ==> arr[k] != 0
    requires forall k :: writeIndex <= k < arr.Length ==> arr[k] == 0
    ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
{
    forall i, j | 0 <= i < j < arr.Length && arr[i] == 0
    ensures arr[j] == 0
    {
        assert i >= writeIndex;
        assert j >= writeIndex;
        assert arr[j] == 0;
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    var writeIndex := 0;
    var readIndex := 0;
    
    ghost var originalArray := arr[..];
    
    while readIndex < arr.Length
        invariant 0 <= writeIndex <= readIndex <= arr.Length
        invariant forall k :: 0 <= k < writeIndex ==> arr[k] != 0
        invariant multiset(arr[..]) == multiset(originalArray)
        invariant forall n, m :: (0 <= n < m < readIndex && originalArray[n] != 0 && originalArray[m] != 0) ==>
                  (exists k, l :: 0 <= k < l < writeIndex && arr[k] == originalArray[n] && arr[l] == originalArray[m])
    {
        if arr[readIndex] != 0 {
            if writeIndex != readIndex {
                swap(arr, writeIndex, readIndex);
            }
            writeIndex := writeIndex + 1;
        }
        readIndex := readIndex + 1;
    }
    
    var finalWriteIndex := writeIndex;
    
    while writeIndex < arr.Length
        invariant finalWriteIndex <= writeIndex <= arr.Length
        invariant forall k :: 0 <= k < finalWriteIndex ==> arr[k] != 0
        invariant forall k :: finalWriteIndex <= k < writeIndex ==> arr[k] == 0
        invariant multiset(arr[..]) == multiset(originalArray)
        invariant forall n, m :: (0 <= n < m < arr.Length && originalArray[n] != 0 && originalArray[m] != 0) ==>
                  (exists k, l :: 0 <= k < l < finalWriteIndex && arr[k] == originalArray[n] && arr[l] == originalArray[m])
    {
        arr[writeIndex] := 0;
        writeIndex := writeIndex + 1;
    }
    
    OrderPreservationAfterLoop(arr, originalArray, finalWriteIndex);
    ZeroClusterAfterSecondLoop(arr, finalWriteIndex);
}
// </vc-code>


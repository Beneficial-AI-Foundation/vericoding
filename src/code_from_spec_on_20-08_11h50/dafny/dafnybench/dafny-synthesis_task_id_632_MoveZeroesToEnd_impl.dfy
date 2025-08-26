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
    ghost var oldArr := arr[..];
    var writePos := 0;
    
    // First pass: move all non-zero elements to the front
    var readPos := 0;
    while readPos < arr.Length
        invariant 0 <= readPos <= arr.Length
        invariant 0 <= writePos <= readPos
        invariant writePos <= arr.Length
        invariant forall i :: 0 <= i < writePos ==> arr[i] != 0
        invariant forall i :: 0 <= i < readPos && oldArr[i] != 0 ==> 
            exists j :: 0 <= j < writePos && arr[j] == oldArr[i]
        invariant forall i :: 0 <= i < writePos ==> 
            exists j :: 0 <= j < readPos && oldArr[j] == arr[i]
        // Order preservation for processed elements
        invariant forall n, m :: 0 <= n < m < readPos && oldArr[n] != 0 && oldArr[m] != 0 ==>
            exists k, l :: 0 <= k < l < writePos && arr[k] == oldArr[n] && arr[l] == oldArr[m]
    {
        if arr[readPos] != 0 {
            arr[writePos] := arr[readPos];
            writePos := writePos + 1;
        }
        readPos := readPos + 1;
    }
    
    // Second pass: fill remaining positions with zeros
    ghost var nonZeroCount := writePos;
    while writePos < arr.Length
        invariant nonZeroCount <= writePos <= arr.Length
        invariant forall i :: 0 <= i < nonZeroCount ==> arr[i] != 0
        invariant forall i :: nonZeroCount <= i < writePos ==> arr[i] == 0
        invariant forall i :: 0 <= i < nonZeroCount ==> 
            exists j :: 0 <= j < |oldArr| && oldArr[j] == arr[i]
        invariant forall i :: 0 <= i < |oldArr| && oldArr[i] != 0 ==> 
            exists j :: 0 <= j < nonZeroCount && arr[j] == oldArr[i]
        // Order preservation
        invariant forall n, m :: 0 <= n < m < |oldArr| && oldArr[n] != 0 && oldArr[m] != 0 ==>
            exists k, l :: 0 <= k < l < nonZeroCount && arr[k] == oldArr[n] && arr[l] == oldArr[m]
    {
        arr[writePos] := 0;
        writePos := writePos + 1;
    }
    
    // The multiset property follows from the construction
    assert forall x :: x in multiset(arr[..]) <==> x in multiset(oldArr);
    assert forall x :: multiset(arr[..])[x] == multiset(oldArr)[x];
}
// </vc-code>

// <vc-helpers>
method swap(arr: array<int>, i: int, j: int)
    requires arr.Length > 0
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    modifies arr
    ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
    ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{
        var tmp := arr[i];
        arr[i] := arr[j];
        arr[j] := tmp;
}

function count(arr: seq<int>, value: int) : (c: nat)
    ensures c <= |arr|
{
    if |arr| == 0 then 0 else (if arr[0] == value then 1 else 0) + count(arr[1..], value)
}

function countZeros(arr: seq<int>) : (c: nat)
    ensures c <= |arr|
{
    if |arr| == 0 then 0 else (if arr[0] == 0 then 1 else 0) + countZeros(arr[1..])
}

function countNonZeros(arr: seq<int>) : (c: nat)
    ensures c <= |arr|
{
    if |arr| == 0 then 0 else (if arr[0] != 0 then 1 else 0) + countNonZeros(arr[1..])
}

function zerosInSeq(s: seq<int>): seq<int>
{
    if |s| == 0 then []
    else if s[0] == 0 then [0] + zerosInSeq(s[1..])
    else zerosInSeq(s[1..])
}

function zerosInRange(s: seq<int>, start: int, end: int): seq<int>
    requires 0 <= start <= end <= |s|
{
    zerosInSeq(s[start..end])
}

function zerosOfLength(n: nat): seq<int>
    ensures |zerosOfLength(n)| == n
    ensures forall i :: 0 <= i < n ==> zerosOfLength(n)[i] == 0
{
    if n == 0 then [] else [0] + zerosOfLength(n-1)
}

lemma multisetConcatLemma(s1: seq<int>, s2: seq<int>, m1: multiset<int>, m2: multiset<int>)
    requires multiset(s1) == m1
    requires multiset(s2) == m2
    ensures multiset(s1 + s2) == m1 + m2
{
    // Dafny can prove this automatically
}

function zeros(n: nat): seq<int>
{
    if n == 0 then [] else [0] + zeros(n-1)
}
// </vc-helpers>
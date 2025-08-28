/**
 * Remove odd numbers from an array of numbers
 **/

predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>
lemma InSeqAfterAppend<T>(s: seq<T>, x: T, y: T)
    requires x in s
    ensures x in s + [y]
{
}

lemma InArraySlice(arr: array<int>, i: int)
    requires 0 <= i < arr.Length
    ensures arr[i] in arr[..]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method RemoveOddNumbers(arr: array<int>) returns (evenList: seq<int>)
    // All numbers in the output are even and exist in the input 
    ensures forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]
    // All even numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    evenList := [];
    var i := 0;
    
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < |evenList| ==> IsEven(evenList[j]) && evenList[j] in arr[..]
        invariant forall j :: 0 <= j < i && IsEven(arr[j]) ==> arr[j] in evenList
    {
        if IsEven(arr[i]) {
            InArraySlice(arr, i);
            evenList := evenList + [arr[i]];
        }
        i := i + 1;
    }
}
// </vc-code>
